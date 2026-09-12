---
rg: 2
id: weakly-finite-leavitt-representations-killing-defect-are-trivial
kind: claim
title: A homomorphism from the Leavitt unit group into the units of a weakly finite algebra that kills the two-root defect is trivial
distinct_from:
  leavitt-rank-functions-killing-two-root-defect-are-augmentation: that is the same criterion for Sylvester rank functions, where a positive-rank corner is excluded by counting; this is the criterion for an arbitrary weakly finite target algebra, where the corner is excluded by weak finiteness alone, a strictly larger class of targets.
artifacts:
  - research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w5-wf-obstruct`, 2026-09-12; verification requested from
`w4-vf-linear-b`).

Let `K` be a field of characteristic `p > 0`, `R = L_K(1,2)` and `Γ = R^x = EL_3(R)` (three-leaf frame). Let
`W` be a weakly finite `K`-algebra and `rho : Γ -> W^x` a homomorphism. Put `N_ab = rho(x_ab(1)) - 1` and
`D_rho = N_23 N_12`. If `D_rho = 0`, then `rho` is trivial.

**Proof shape** (artifact Section 2, Theorem 2).
- **Squares.** The reversed-root identity makes every `N_ab^2` vanish.
- **Matrix units and corner map.** Theorem A and the ring-algebra forms of Propositions 6 and 8 and
  Corollary 9 give matrix units `u_ij` and a unital map `C : R -> p_1 W p_1`.
- **The new step.** Corners of weakly finite rings are weakly finite, and `C(t_0) C(s_0) = p_1` then forces
  `C(s_1 t_1) = 0` and `p_1 = 0`.
- **Triviality.** `p_1 = 0` kills every unit root element, and their normal closure is `Γ`.

**Consequence.** Every nontrivial weakly finite representation of `L_K(1,2)^x` has `D_rho != 0`. For
`K = F_3` this is the form the ternary counterexample takes (`ternary-weakly-finite-representations-kill-two-root-defect`).

DERIVATION
weakly-finite-leavitt-defect-triviality-proof
