---
rg: 2
id: sylvester-near-minimal-leavitt-defects-are-multiplicative
kind: claim
title: Near-minimal Sylvester rank functions on the binary Leavitt unit group algebra have multiplicative disjoint-cylinder defects
distinct_from:
  near-minimal-defect-models-have-multiplicative-cylinder-defects: that is near-minimal multiplicativity for rank-ultraproduct models, through kernel corners; this is the same statement for every Sylvester rank function, normalized by the augmentation quotient, where no kernel corner exists.
artifacts:
  - research/artifacts/sylvester-class-a-defect-chain-2026-09-12.md
---

**OPEN.** Let `R = L_(F_2)(1,2)` and `c_*^Syl = inf rho_omega(D_1000)` over non-augmentation Sylvester rank
functions `rho` on `F_2[R^x]`; it is at least `c_0 > 0` by `sylvester-leavitt-defect-gap-and-geometric-descent`.
If `delta = rho_omega(D_1000) <= (1 + eps) c_*^Syl`, then for pairwise disjoint proper cylinders
`A_1, ..., A_k`, `|rho_omega(D_(A_1) ... D_(A_k)) - delta^k| <= 2 eps delta`.

**Why it matters.** With a Sylvester-form strict submultiplicativity bound
`rho_omega(D_A D_B) <= theta rho_omega(D_A) rho_omega(D_B)`, `theta < 1`, the computation of Consequence 3.2 of
`research/artifacts/rank-gate-axiom-audit-2026-09-12.md` excludes near-minimizers, which exist by compactness. So
every Sylvester rank function kills the two-root defect: `sylvester-rank-functions-on-leavitt-units-kill-two-root-defect`,
with no regularity and no matrix approximation.

## Attempts

- 2026-09-12 `w5-regular-rankfn` (artifact Section 5.2). Two inputs of the regular proof (Proposition 4.1 of
  `research/artifacts/two-root-defect-descent-gap-2026-09-12.md`) are missing in class (A).
  - **Exact globality,** for the lower bound with constant `c_*^Syl`: `sylvester-leavitt-kazhdan-fixed-ideals-are-global`.
  - **A kernel corner.** The regular proof compresses to the right annihilator of the defect product. Sylvester
    rank functions compress to quotients by two-sided ideals and to images of commuting elements
    (`sylvester-rank-functions-descend-to-quotients-and-compressions`). A right annihilator of a non-central element
    is neither, and the triangular axiom only bounds the kernel part from above.
  - Regularity of every rank function (`sylvester-rank-functions-on-leavitt-units-are-regular`) would supply both.
