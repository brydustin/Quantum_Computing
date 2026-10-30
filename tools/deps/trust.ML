(* Trusted base of a theorem: the constants and types of its statement, closed under
   definitional dependencies (Defs.get_deps) through items defined in our sessions
   (theory long name with a prefix in TRUST_OURS); items from elsewhere are leaves.
   TRUST_FACTS = comma-separated theory:fact.  TSV to TRUST_OUT:
   target, kind, name, owner theory, file, line, ours. *)
val ours = space_explode "," (getenv "TRUST_OURS");
fun is_ours thy_name = exists (fn p => String.isPrefix p thy_name) ours;
fun add_tycons (Type (a, Ts)) = insert (op =) a #> fold add_tycons Ts
  | add_tycons _ = I;
fun entry_of thy (Defs.Const, c) = Name_Space.the_entry (Consts.space_of (Sign.consts_of thy)) c
  | entry_of thy (Defs.Type, a) = Name_Space.the_entry (Type.type_space (Sign.tsig_of thy)) a;
fun pos_of (e: Name_Space.entry) = (case #pos_history e of p :: _ => p | [] => Position.none);
fun do_target spec =
  let
    val (thy_name, fact) = (case space_explode ":" spec of [a, b] => (a, b) | _ => error spec);
    val thy = Build.get_theory thy_name;
    val ctxt = Proof_Context.init_global thy;
    val props = map Thm.prop_of (Proof_Context.get_thms ctxt fact);
    val items0 =
      map (pair Defs.Const) (fold Term.add_const_names props []) @
      map (pair Defs.Type) (fold (Term.fold_types add_tycons) props []);
    val defs = Theory.defs_of thy;
    fun visit item (seen, acc) =
      if member (op =) seen item then (seen, acc)
      else
        let
          val e = entry_of thy item;
          val own = is_ours (#theory_long_name e);
          val acc' = (item, e, own) :: acc;
          fun def_items name =
            let val prop = Thm.prop_of (Thm.axiom thy name)
            in map (pair Defs.Const) (Term.add_const_names prop []) @
               map (pair Defs.Type) (Term.fold_types add_tycons prop []) end
            handle ERROR _ => [];
          val next =
            if own then
              maps (fn s => (case #def s of SOME n => def_items n | NONE => []))
                (Defs.specifications_of defs item)
            else [];
        in fold visit next (item :: seen, acc') end;
    val (_, found) = fold visit items0 ([], []);
    fun row ((kind, name), e, own) =
      space_implode "\t" [spec, (case kind of Defs.Const => "const" | Defs.Type => "type"), name,
        #theory_long_name e, the_default "" (Position.file_of (pos_of e)),
        string_of_int (the_default 0 (Position.line_of (pos_of e))), if own then "1" else "0"];
  in map row found end;
val rows = maps do_target (space_explode "," (getenv "TRUST_FACTS"));
val _ = File.write (Path.explode (getenv "TRUST_OUT")) (cat_lines rows ^ "\n");
val _ = writeln ("trust rows " ^ string_of_int (length rows));
