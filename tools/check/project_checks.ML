(* Checks for the project's theories: oracles, duplicate facts and definitions, name clashes.
   Theories are identified by session.  "audit" sessions are checked for oracles other than the
   "allow"ed ones; "targets" are checked for redundancy against everything else in the context
   except the "ignore" sessions.
   The report goes to output/NAME.txt; with "strict" any problem fails the build. *)

structure Project_Checks =
struct

fun canon t =
  let
    val t = Envir.beta_eta_contract t
    val tvars = rev (Term.add_tvars t [])
    val tmap = map_index (fn (i, (v, _)) => (v, ("'t" ^ string_of_int i, 0))) tvars
    fun renT (TVar (v, _)) = TVar (the (AList.lookup (op =) tmap v), [])
      | renT T = T
    val t = Term.map_types (Term.map_atyps renT) t
    val vars = rev (Term.add_vars t [])
    val vmap = map_index (fn (i, (v, _)) => (v, ("v" ^ string_of_int i, 0))) vars
    fun ren (Var (v, T)) = Var (the (AList.lookup (op =) vmap v), T)
      | ren a = a
  in Term.map_aterms ren t end;

fun sym_eq (Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, T) $ a $ b)) =
      SOME (HOLogic.mk_Trueprop (Const (\<^const_name>\<open>HOL.eq\<close>, T) $ b $ a))
  | sym_eq _ = NONE;

val generated = ["_def", "simps", "cases", "induct", "intros", "elims", "eqns", "cong", "split", "split_asm",
  "inject", "distinct", "exhaust", "rec", "case", "sel", "collapse", "nchotomy", "eq", "pinduct", "psimps",
  "transfer", "size", "size_gen", "code"];
fun is_generated n = exists (fn s => String.isSuffix s n) generated;

(* session of each theory in the context, by base name *)
fun session_table thy =
  fold (fn t => Symtab.update (Context.theory_base_name t, Long_Name.qualifier (Context.theory_long_name t)))
    (thy :: Theory.ancestors_of thy) Symtab.empty;

(* definition bodies are compared without types, so specialisations of polymorphic
   definitions count as duplicates *)
val erase = Term.map_types (K dummyT);

fun def_body th =
  let
    val (l, r) = (case Thm.prop_of th of
        Const (\<^const_name>\<open>Pure.eq\<close>, _) $ l $ r => (l, r)
      | Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ l $ r) => (l, r)
      | _ => raise Match)
    val (h, args) = strip_comb l
    val _ = (case h of Const _ => () | _ => raise Match)
    val _ = if forall is_Var args andalso not (has_duplicates (op aconv) args) then () else raise Match
    val _ = if String.isSubstring "_class." (fst (dest_Const h)) then raise Match else ()
    val _ = if Term.size_of_term r <= 3 then raise Match else ()
  in SOME (fst (dest_Const h), erase (canon (fold_rev (fn x => fn t => Term.lambda x t) args r))) end
  handle Match => NONE;

fun run {name, audit, allow, targets, ignore, strict} thy =
  let
    val stab = session_table thy
    fun sess_of n = Symtab.lookup stab (hd (Long_Name.explode n))
    fun in_sessions ss n = (case sess_of n of SOME s => member (op =) ss s | NONE => false)
    val facts = Facts.dest_static false [] (Global_Theory.facts_of thy)
    val out = Unsynchronized.ref ([] : string list)
    fun say s = out := s :: ! out
    val fails = Unsynchronized.ref 0
    fun fail s = (say s; fails := ! fails + 1)

    (* oracles *)
    val afacts = filter (in_sessions audit o fst) facts
    fun oracles ths = distinct (op =) (map (#1 o #1) (Thm_Deps.all_oracles (map (Thm.transfer thy) ths)))
    val with_oracles = filter (fn (_, ths) => not (null (oracles ths))) afacts
    val bad = filter (fn (_, ths) => exists (fn x => not (member (op =) allow x)) (oracles ths)) with_oracles
    val nthms = length (maps snd afacts)
    val _ = say ("AUDIT " ^ commas audit ^ ": " ^ string_of_int (length afacts) ^ " facts, " ^
      string_of_int nthms ^ " theorems, " ^ string_of_int (length with_oracles) ^ " with oracles" ^
      (if null allow then "" else " (allowed: " ^ commas allow ^ ")"))
    val _ = List.app (fn (n, ths) => say ("allowed oracle in " ^ n ^ ": " ^ commas (oracles ths)))
      (subtract (op = o apply2 fst) bad with_oracles)
    val _ = List.app (fn (n, ths) => fail ("ORACLE " ^ n ^ ": " ^ commas (oracles ths))) bad

    (* duplicate facts *)
    val is_target = in_sessions targets
    val (tf, lf) = List.partition (is_target o fst) facts
    val lf = filter (not o in_sessions ignore o fst) lf
    val loc_names = map Long_Name.base_name (Locale.get_locales thy)
    fun top_or_locale n = (case Long_Name.explode n of
        [_, _] => true
      | [_, l, _] => member (op =) loc_names l
      | _ => false)
    val tf = filter (fn (n, _) => not (is_generated n) andalso top_or_locale n) tf
    val ltab = fold (fn (n, ths) => fold (fn th => Termtab.cons_list (canon (Thm.prop_of th), n)) ths) lf Termtab.empty
    fun hits th =
      Termtab.lookup_list ltab (canon (Thm.prop_of th)) @
      (case sym_eq (Thm.prop_of th) of SOME q => Termtab.lookup_list ltab (canon q) | NONE => [])
    val _ = tf |> List.app (fn (n, ths) => ths |> List.app (fn th =>
      (case distinct (op =) (hits th) of [] => () | ls => fail ("DUP " ^ n ^ " == " ^ commas (take 4 ls)))))
    val ttab = fold (fn (n, ths) => fold (fn th => Termtab.cons_list (canon (Thm.prop_of th), n)) ths) tf Termtab.empty
    val _ = Termtab.fold (fn (_, ns) => fn () =>
      let val ns' = distinct (op =) ns in if length ns' > 1 then fail ("INNER " ^ commas ns') else () end) ttab ()

    (* duplicate definitions *)
    val defs = facts |> filter (fn (n, _) => String.isSuffix "_def" n)
      |> maps (fn (n, ths) => map_filter (fn th => Option.map (fn (c, b) => (n, c, b)) (def_body th)) ths)
    val (tdefs, ldefs) = List.partition (fn (n, _, _) => is_target n) defs
    val ldefs = filter (fn (n, _, _) => not (in_sessions ignore n)) ldefs
    val dtab = fold (fn (_, c, b) => Termtab.cons_list (b, c)) ldefs Termtab.empty
    val _ = tdefs |> List.app (fn (_, c, b) =>
      (case distinct (op =) (Termtab.lookup_list dtab b) of [] => () | cs => fail ("DEFDUP " ^ c ^ " == " ^ commas (take 4 cs))))
    val tdtab = fold (fn (_, c, b) => Termtab.cons_list (b, c)) tdefs Termtab.empty
    val _ = Termtab.fold (fn (_, cs) => fn () =>
      let val cs' = distinct (op =) cs in if length cs' > 1 then fail ("DEFINNER " ^ commas cs') else () end) tdtab ()

    (* name clashes with another fact or constant of the same base name (locale-internal names excepted) *)
    val locales = map Long_Name.base_name (Locale.get_locales thy)
    fun base_access _ n = not (member (op =) locales (Long_Name.base_name (Long_Name.qualifier n)))
    val fspace = ()
    val cspace = ()
    val lnames = fold (fn (n, _) => if base_access fspace n then Symtab.cons_list (Long_Name.base_name n, n) else I)
      lf Symtab.empty
    val _ = tf |> List.app (fn (n, _) =>
      (case Symtab.lookup_list lnames (Long_Name.base_name n) of [] => ()
        | ls => fail ("FACTCLASH " ^ n ^ " ~ " ^ commas (take 3 ls))))
    val consts = map fst (#constants (Consts.dest (Sign.consts_of thy)))
    val record_names = ["make", "fields", "extend", "truncate", "more", "more_update"]
    val consts = filter (fn n => not (member (op =) record_names (Long_Name.base_name n))) consts
    val (tc, lc) = List.partition is_target consts
    val lc = filter (not o in_sessions ignore) lc
    val lcn = fold (fn n => if base_access cspace n then Symtab.cons_list (Long_Name.base_name n, n) else I)
      lc Symtab.empty
    val _ = tc |> List.app (fn n =>
      (case Symtab.lookup_list lcn (Long_Name.base_name n) of [] => ()
        | ls => fail ("CONSTCLASH " ^ n ^ " ~ " ^ commas (take 3 ls))))

    (* same conclusion, different premises: reported, not failed *)
    val ctab = fold (fn (n, ths) => fold (fn th =>
      Termtab.cons_list (canon (Logic.strip_imp_concl (Thm.prop_of th)), n)) ths) tf Termtab.empty
    val _ = Termtab.fold (fn (_, ns) => fn () =>
      let val ns' = distinct (op =) ns in if length ns' > 1 then say ("note: same conclusion " ^ commas ns') else () end) ctab ()

    val _ = say ("TARGETS " ^ commas targets ^ ": " ^ string_of_int (length tf) ^ " facts, " ^
      string_of_int (length tdefs) ^ " definitions, " ^ string_of_int (length tc) ^ " constants")
    val report = rev (! out)
    val dir = Path.append (Resources.master_directory thy) (Path.explode "../output")
    val _ = Isabelle_System.make_directory dir
    val _ = File.write (Path.append dir (Path.basic (name ^ ".txt"))) (cat_lines report ^ "\n")
    val _ = List.app writeln report
  in
    if ! fails = 0 orelse not strict then () else error (name ^ ": " ^ string_of_int (! fails) ^ " problems, see output/" ^ name ^ ".txt")
  end;

end;
