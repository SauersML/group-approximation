---
rg: 2
id: fpbs-homogeneous-group-ring-symbols-l2-injective
kind: claim
title: One minus a homogeneous group-ring element is injective with dense range on l2
distinct_from:
  fpbs-amen2-betti-cost-input: that is Gaboriau's inequality between cost and the first L2 Betti number; this is an operator lemma that certifies injectivity of stage maps on L2-homology without Linnell's theorem or L2-independence.
artifacts:
  - research/artifacts/fpbs-finite-contact-obstruction-2026-09-17.md
  - experiments/fpbs-locally-free-malnormal-union-2026-09-17/fox_homogeneity.py
---

**ESTABLISHED.** Let `G` be a countable group with a homomorphism
`ht : G -> Z`. Let `T = sum_i c_i g_i` be a finite element of `CG` whose
support elements all have height `m != 0`.
- **Operators.** Left and right multiplication by `1 - T` are injective with
  dense range on `ℓ²G`.
- **Group von Neumann algebra.** `u -> u lambda(1 - T)` is injective on
  `N(G)`.
- **Supergroups.** Both statements pass to every group `Gamma >= G` through
  the coset decomposition of `ℓ²Gamma`. Only `G` needs a height function.

**Application.** For
`Gamma_mal = lim(F_2 -> F_2 -> ...)` along `a -> a`, `b -> b a b^{-2}`, the
stage Fox matrix is `[[1, 0], [b, 1 - b a b^{-1} - b a b^{-2}]]`. The entry
`1 - b a b^{-1} - b a b^{-2}` has the required form for `ht(a) = 1`,
`ht(b) = 0`; the script recomputes this. So the stage maps on first
`L²`-homology are injective, and Lück's colimit theorem gives
`beta_1^(2)(Gamma_mal) = 1` (artifact §3, Proposition 5). This is an
elementary cross-check of the locally free case of `beta_1 = c* - 1`.
