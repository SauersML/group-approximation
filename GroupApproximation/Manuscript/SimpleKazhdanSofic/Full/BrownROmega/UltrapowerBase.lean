import GroupApproximation.Analysis.MatrixUltraproductToHyperfiniteUltrapower

/-!
# Brown's formulation: the ultrapower infrastructure

`simple_kazhdan_sofic_group.tex`, subsection "Brown's formulation": "`L(G)` embeds in `𝓡^ω`" and
"`L(G) ⊗̄ 𝓡` ... embeds in `𝓡^ω`".

This module only brings the tracial ultrapower infrastructure into the build, as a step of its
own, for the `𝓡^ω` embedding files of this lane:

* `TracialUltrapower.Ultrapower τ ω`, the tracial ultrapower `M^ω` of a von Neumann algebra with a
  tracial vector, with its ultratrace and the diagonal embedding `M → M^ω`;
* `Hyperfinite.HyperfiniteUltrapower ω`, which is `𝓡^ω`;
* `Hyperfinite.matrixUltraproductToHyperfiniteUltrapower`, the unital trace-preserving
  `⋆`-homomorphism `∏_ω M_k → 𝓡^ω`.
-/
