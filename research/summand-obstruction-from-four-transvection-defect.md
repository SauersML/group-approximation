---
rg: 2
id: summand-obstruction-from-four-transvection-defect
kind: route
title: Defect vanishing on the five-generator subgroup makes every anti-central weakly finite image zero
target: ternary-anti-central-summand-has-no-weakly-finite-image
requires:
  - four-transvections-and-x23-force-defect-vanishing
  - weakly-finite-leavitt-representations-killing-defect-are-trivial
artifacts:
  - research/artifacts/four-transvection-escape-set-2026-09-12.md
---
Artifact Section 5, item 1. OPEN while `four-transvections-and-x23-force-defect-vanishing` is open.
1. A unital `ψ : S_- -> W` into a weakly finite `W` gives `ρ(g) = ψ(ε_- g)`, a homomorphism `G -> W^x` with
   `ρ(z) = -1`.
2. The restriction of `ρ` to `Γ_5` has `D_ρ = 0`, by the open claim. `D_ρ` involves only `x_12(1)` and `x_23(1)`, so it
   is the same element for `ρ` on `G`.
3. So `ρ` is trivial, by `weakly-finite-leavitt-representations-killing-defect-are-trivial`.
4. Then `-1 = ρ(z) = 1` in `W`, so `2 = 0` and, in characteristic three, `W = 0`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 36.5 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS as an implication. OPEN while `four-transvections-and-x23-force-defect-vanishing` is open.*
