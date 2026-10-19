chapter AFP

session Vern_Paulsen_QC_3_10 in "." = Isabelle_Marries_Dirac +
  options [quick_and_dirty = false, timeout = 3600]
  sessions
    Quantum_Fourier_Transform
    "HOL-Hahn_Banach"
    "HOL-Analysis"
  theories
    "HOL-Analysis.Euclidean_Space"
    "HOL-Analysis.L2_Norm"
    "HOL-Analysis.Elementary_Metric_Spaces"
    "HOL-Analysis.Topology_Euclidean_Space"
    Basic_Math
    Quantum_Computing_3_10
    "HOL-Hahn_Banach.Hahn_Banach"
    Matrix_Typed
    Essential_Functional_Analysis

session Vern_Paulsen_QC_3_10_Lmat in "Lmat" = Vern_Paulsen_QC_3_10 +
  options [quick_and_dirty = false, timeout = 3600]
  theories
    Lmat_Euclidean
    Separable_Cone

session Vern_Paulsen_QC in Day11 = Vern_Paulsen_QC_3_10_Lmat +
  options [quick_and_dirty = false, timeout = 3600]
  theories
    Quantum_Computing11
    Day23_ChoiExtremeUCP
    Day24_Separability
    QC_Prelims
    Day12_Counting_Probability
    Day18_Positive_Maps
    Day22_Kraus_Independence
    Day28_Horodecki_Peres
    Day30_BitFlip_Code
    Day32_Pauli_Expansion

session Vern_Paulsen_QC_Notes in "notes_doc" = Vern_Paulsen_QC +
  description "
    Paulsen's lecture notes, formalised: the document session that typesets
    all project theories with proofs folded (document/output/document.pdf)."
  options [document = pdf, document_output = "output",
           document_variants = "document=/proof,/ML",
           quick_and_dirty = false, timeout = 3600]
  theories
    QC_Notes_Overview
  document_theories
    Vern_Paulsen_QC_3_10.Basic_Math
    Vern_Paulsen_QC_3_10.Quantum_Computing_3_10
    Vern_Paulsen_QC_3_10.Matrix_Typed
    Vern_Paulsen_QC_3_10.Essential_Functional_Analysis
    Vern_Paulsen_QC_3_10_Lmat.Lmat_Euclidean
    Vern_Paulsen_QC_3_10_Lmat.Separable_Cone
    Vern_Paulsen_QC.Quantum_Computing11
    Vern_Paulsen_QC.Day23_ChoiExtremeUCP
    Vern_Paulsen_QC.Day24_Separability
    Vern_Paulsen_QC.QC_Prelims
    Vern_Paulsen_QC.Day12_Counting_Probability
    Vern_Paulsen_QC.Day18_Positive_Maps
    Vern_Paulsen_QC.Day22_Kraus_Independence
    Vern_Paulsen_QC.Day28_Horodecki_Peres
    Vern_Paulsen_QC.Day30_BitFlip_Code
    Vern_Paulsen_QC.Day32_Pauli_Expansion
  document_files
    "root.tex"
