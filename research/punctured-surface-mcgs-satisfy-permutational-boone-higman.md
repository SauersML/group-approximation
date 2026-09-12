---
rg: 2
id: punctured-surface-mcgs-satisfy-permutational-boone-higman
kind: claim
title: Mapping class groups of surfaces with a puncture or boundary, and of closed surfaces of genus at most two, lie in the permutational Boone--Higman class
distinct_from:
  aut-free-groups-satisfy-permutational-boone-higman: that imports Theorem A, the embedding of Aut(F_n), and mentions Corollary B only in prose; this imports the mapping class group case of Corollary B, together with the conclusion of its proof that these groups satisfy the permutational form, which is what closure arguments over finite-index subgroups consume.
artifacts:
  - research/artifacts/bh-out-fn-closed-mcg-2026-09-12.md
---

**ESTABLISHED (literature import).** Belk--Fournier-Facio--Hyde--Zaremsky,
arXiv:2503.21882v2, Corollary B, first bullet. Read on 2026-09-12 from the PDF,
extracted on MSI. The following groups satisfy the Boone--Higman conjecture:

> "The (extended) mapping class group of an orientable surface Σ of finite type,
> where Σ either has non-empty boundary, at least one puncture, and/or genus at
> most two."

The proof in their Section 4 gives more: each such group satisfies PBH, i.e.
lies in the class `B_A` of `boone-higman-type-a-class-closed-under-finite-extensions`.
- **At least two punctures.** `MCG(Σ, ∗)` embeds in `Aut(π1(Σ))` by
  Dehn--Nielsen--Baer, which is `Aut(F_n)`, and it has finite index in
  `MCG(Σ ∖ {∗})`.
- **One puncture.** A finite-index subgroup `L ≤ MCG(Σ∗)` lifts to the double
  cover with two punctures, "injective by a version of the Birman–Hilden
  Theorem [ALS09, Corollary 4]", and "this proves PBH for MCG(Σ∗)".
- **Boundary.** Attach a twice-punctured disk to every boundary component.
- **Genus two.** Quotient by the central hyperelliptic involution gives the
  mapping class group of the six-punctured sphere, and residual finiteness
  gives "MCG(Σ) is commensurable to MCG(Σ′), which satisfies PBH."

**Not covered: closed surfaces of genus at least three.** From the same paper:
"For mapping class groups, the conjecture remains open for closed surfaces of
genus at least three." That open case is
`closed-surface-mapping-class-groups-satisfy-boone-higman`.
