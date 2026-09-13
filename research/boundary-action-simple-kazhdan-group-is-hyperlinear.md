---
rg: 2
id: boundary-action-simple-kazhdan-group-is-hyperlinear
kind: claim
title: The boundary simple Kazhdan group S_∂ = EL_N(LC(∂F_2,k) ⋊ F_2)/Z over a finite field is hyperlinear
distinct_from:
  binary-leavitt-unit-group-hyperlinear: that asks for HS models of L_(F_2)(1,2)^x or EL_D over it; this asks for HS models of the larger boundary group, which contains EL_N(L_k(1,2)) meeting no central scalars, so a positive answer here gives one there.
  boundary-action-simple-kazhdan-group-is-nonsofic: that is the established nonsoficity of the same group; this is its open hyperlinearity.
---

OPEN. Let `k` be a finite field, `N >= 3` and `S_∂ = EL_N(LC(∂F_2, k) ⋊ F_2)/Z(EL_N)`. Is `S_∂` hyperlinear?

- **Positive answer.** It is nonsofic (`boundary-action-simple-kazhdan-group-is-nonsofic`), so it would be a
  hyperlinear nonsofic simple Kazhdan group, which answers Pestov Question 3.4 negatively.
- **Negative answer.** It would be an explicit non-hyperlinear group. No such group is known.

## Attempts

- **Operator-norm transport in HS norm.** It dies at the first step of Thm l.478: `||Ad(A)-Ad(B)|| <= 2||A-B||_op`
  has no Hilbert–Schmidt analogue. `D_d = diag(-1,1,...,1)` has `||D_d-1||_2 -> 0` while `||Ad(D_d)-id|| = 2`, so the
  corona homomorphism and its Kazhdan projection do not exist.
  - The tracial substitute gives `U^*PU <= P` in `B(L^2(prod_U M_n))`, which is not finite, so equality can fail.
  - The tex's sofic group `W` (l.1844) shows the defect conclusion does fail in HS norm.
  - The exact group-level replacement is the open win-win `hyperlinear-groups-kill-rigid-compression-defects`.
  - Artifact `research/artifacts/un-hyperlinear-paradox-2026-09-13.md` §3.
- **Sofic-type models** (permutation, Păunescu partial actions, random lifts). Dead over finite `k` by the
  established nonsoficity. Any HS model must be non-permutational.
- **Reduction to the Leavitt case.** `L_k(1,2) ↪ LC(∂F_2,k) ⋊ F_2` unitally, and the corner trick puts
  `EL_N(L_k(1,2))` inside `S_∂` meeting no central scalars. A positive answer here would make `EL_N(L_k(1,2))`
  hyperlinear. This direction is no easier than `binary-leavitt-unit-group-hyperlinear` (artifact §4).
- **Characteristic 0.** Over `Q` the Lean nonsoficity theorem does not apply. Reduction mod `p` gives only quotient
  maps, which transfer nothing, so soficity over `Q` is also undecided.
