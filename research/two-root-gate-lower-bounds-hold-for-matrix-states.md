---
rg: 2
id: two-root-gate-lower-bounds-hold-for-matrix-states
kind: claim
title: The two-root defect criterion and the characteristic-three gap and descent lower bounds hold for matrix states, which exist exactly under the rank condition
distinct_from:
  leavitt-rank-functions-killing-two-root-defect-are-augmentation: that is the criterion for Sylvester matrix rank functions, which satisfy the triangular axiom; this proves it for matrix states (normalized, additive, minor-monotone) with no triangular axiom, so it applies over every ring with the rank condition.
  weakly-finite-leavitt-representations-killing-defect-are-trivial: that is the criterion for representations into weakly finite algebras; this applies it to null quotients of matrix states, which push-through makes weakly finite.
  ternary-anti-central-two-root-defect-has-a-uniform-gap: that is the gap over anti-central Sylvester rank functions, including the upper bound 2/3; this is the lower-bound half over anti-central matrix states, whose minimum can only be smaller and which obey no Jordan upper bound.
artifacts:
  - research/artifacts/two-root-certificates-separate-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w6-upg-separate`, 2026-09-12; verification requested from `w4-vf-linear-b`).

A *matrix state* `d` on a unital ring `A` assigns `d(M) >= 0` to every rectangular matrix, with `d(I_1) = 1`,
`d(X (+) Y) = d(X) + d(Y)` and `d(XMY) <= d(M)`. No triangular axiom is assumed.

1. **Null quotients.** `ker d = {x : d(x) = 0}` is a proper ideal, `d` descends to a faithful matrix state on
   `A/ker d`, and `A/ker d` is weakly finite.
2. **Two-root criterion.** Let `K` be a field of characteristic `p > 0`, `R = L_K(1,2)` and `Γ = R^x`,
   identified with `EL_3(R)` (`leavitt-gl-equals-el-and-perfect-unit-group`). Let `rho : Γ -> A^x` be a
   homomorphism into a `K`-algebra, `N_ab = rho(x_ab(1)) - 1` and `D_rho = N_23 N_12`. If `d(D_rho) = 0`, then
   `d(rho(g) - 1) = 0` for every `g`. On `K[Γ]` this makes `d` the augmentation rank.
3. **Characteristic three.** Let `G = L_(F_3)(1,2)^x` and `A_mat = {d : d(eps_-) = 1}` on `F_3[G]`.
   - `A_mat` is nonempty iff `S_-` has the rank condition.
   - `A_mat` is compact, and `c_3^mat = min {d(D) : d in A_mat}` is attained and positive. It is at most `c_3`
     when anti-central Sylvester rank functions exist.
   - Compressing `X -> d(phi(X) P)/d(P)` along any `P` that commutes with `phi(A')` gives a matrix state.
   - Every `d` in `A_mat` has `d(Q_A) = 1/2` and `d(D_A Q_A) >= c_3^mat/2` for nonempty proper prefixes `A`.
     Theorems 3.1.2–3.1.4 of `research/artifacts/char-three-defect-gap-and-descent-2026-09-12.md` hold with
     `c_3^mat` in place of `c_3`.

**Not included.** The upper bounds `c_3 <= 2/3` and `f(k+1) <= (2/3) f(k)`. They rest on the Frobenius
inequality, and matrix states can violate them (artifact Example 3.3).

**Consequence.** Outside its target, the route `ternary-rank-kill-via-anti-central-defect-deficit` runs on
`A_mat`. If items 1–2 of `ternary-anti-central-disjoint-defects-have-a-strict-deficit` hold over `A_mat`, then
`S_-` fails the rank condition, with no state upgrade.

Proof: Sections 1 and 2 of the artifact.
