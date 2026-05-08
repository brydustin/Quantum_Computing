chapter AFP

session Vern_Paulsen_QC_3_10 in "." = Isabelle_Marries_Dirac +
  options [document = false, quick_and_dirty = true, timeout = 3600]
  sessions
    Quantum_Fourier_Transform
  theories
    Basic_Math
    Quantum_Computing_3_10

(* Intermediate heap that bundles the Hahn-Banach machinery on top of
   Vern_Paulsen_QC_3_10, so downstream theories can import HB without
   paying for its compilation each time. *)
session Vern_Paulsen_QC_3_10_HB in HB_Heap = Vern_Paulsen_QC_3_10 +
  options [document = false, quick_and_dirty = true, timeout = 3600]
  sessions
    "HOL-Hahn_Banach"
  theories
    "HOL-Hahn_Banach.Hahn_Banach"

session Vern_Paulsen_QC in Day11 = Vern_Paulsen_QC_3_10_HB +
  options [document = false, quick_and_dirty = true, timeout = 3600]
  theories
    Quantum_Computing11
