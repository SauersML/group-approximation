---
rg: 2
id: binary-tensor-square-rank-functions-kill-two-root-defect
kind: claim
title: Rank functions through the binary diagonal tensor square kill the two-root defect, so they only give the augmentation rank
distinct_from:
  sylvester-rank-functions-on-leavitt-units-kill-two-root-defect: that is the open statement for every Sylvester rank function on the binary group algebra; this proves it for the rank functions that factor through the diagonal tensor square, the construction handle named in its artifact.
  binary-tensor-square-rank-functions-live-on-diagonal-norms: that localizes any such rank function on diagonal-block norms; this uses its null off-diagonal norms to kill the defect, whose left support is off-diagonal.
artifacts:
  - research/artifacts/diagonal-tensor-rank-functions-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w4-tensor-rankfn`; verification requested from `w3-vf-linear`) by
`binary-tensor-square-defect-left-support-proof`.

**Setup.** `R = L_(F_2)(1,2)`, `Γ = R^x = EL_3(R)` through the three-leaf code, `D = N_23 N_12`, and
`Δ_2 : F_2[Γ] -> R ⊗ R`, `[g] -> g ⊗ g`.

**Statement.** Every Sylvester matrix rank function on a ring receiving a unital map from `Δ_2(F_2[Γ])` kills
`Δ_2(D)`. So every Sylvester matrix rank function on `F_2[Γ]` that factors through `Δ_2` is the augmentation
rank.

**What this settles and what it leaves.**
- **Dead handle:** `binary-leavitt-units-carry-nonaugmentation-rank-function` cannot be realized by any `W ⊗ W`
  construction. That was the handle `research/artifacts/sylvester-rank-function-two-root-gate-2026-09-12.md`
  Section 3.4 called the only live one.
- **Open:** degrees `n >= 3` in characteristic two, where supports with a repeated set bring back the scalar
  `2`.
