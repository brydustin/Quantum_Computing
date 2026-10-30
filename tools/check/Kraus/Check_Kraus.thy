theory Check_Kraus
  imports Kraus_Maps_Bridge.Kraus_Maps_Bridge
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Kraus", audit = ["Kraus_Maps_Bridge"], allow = ["Types_To_Sets.cancel_type_definition"], targets = ["Kraus_Maps_Bridge"], ignore = [], strict = true} \<^theory>\<close>

end
