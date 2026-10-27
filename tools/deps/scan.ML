(* For every fact of the theories whose long name starts with one of the prefixes in
   the environment variable SCAN_PREFIXES (comma-separated): the named facts its proof
   uses, and the constants and types of its statement.  TSV lines
   theory, fact, dep|const|type, owner theory, name  ->  file SCAN_OUT. *)
val prefixes = space_explode "," (getenv "SCAN_PREFIXES");
val names = Thy_Info.get_names ();
val base_tab = Symtab.make (map (fn n => (Long_Name.base_name n, n)) names);
fun owner q =
  (case Long_Name.explode q of a :: _ => the_default a (Symtab.lookup base_tab a) | [] => "");
fun add_tycons (Type (a, Ts)) = insert (op =) a #> fold add_tycons Ts
  | add_tycons _ = I;
fun scan_thy name =
  let
    val thy = Thy_Info.get_theory name;
    val facts =
      Facts.dest_static false (map Global_Theory.facts_of (Theory.parents_of thy))
        (Global_Theory.facts_of thy);
    fun row kind fact x = space_implode "\t" [name, fact, kind, owner x, x];
    fun do_fact (fact, ths) =
      let
        val deps = Thm_Deps.thm_deps thy ths |> map (fn (_, (n, _)) => n) |> distinct (op =);
        val props = map Thm.prop_of ths;
        val consts = fold Term.add_const_names props [];
        val types = fold (Term.fold_types add_tycons) props [];
      in
        map (row "dep" fact) deps @ map (row "const" fact) consts @ map (row "type" fact) types
      end;
  in maps do_fact facts end;
val selected = filter (fn n => exists (fn p => String.isPrefix p n) prefixes) names;
val _ = File.write (Path.explode (getenv "SCAN_OUT"))
  (cat_lines (maps scan_thy selected) ^ "\n");
val _ = writeln ("scanned " ^ string_of_int (length selected) ^ " theories");
