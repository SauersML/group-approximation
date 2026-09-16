---
rg: 2
id: stw83-circle-ideal-cuntz-quotient-dimension-two-bound
kind: claim
title: The minimal circle-ideal Cuntz-quotient graphs are constant-symbol pullbacks of nuclear dimension one or two
artifacts:
  - research/artifacts/stw99-constant-symbol-pullback-2026-09-16.md
distinct_from:
  stw83-finite-kirchberg-core-circle-quotient-dimension-one: that has the Kirchberg algebra as the ideal and the circle as the quotient, where the value one is known; this is the opposite orientation, where only the range one-or-two is proved.
  stw83-canonical-circle-toeplitz-dimension-two-bound: that is the circle-by-circle entry of the ENSW table; this is the circle-ideal/Kirchberg-quotient entry.
  stw83-two-non-k-extension-directions-remain-open: that records that both entries are open; this gives an explicit pullback model and the one-or-two range for the Kirchberg-quotient entry, without deciding it.
---

For `n>=2` and `k>=1`, let `F_(n,k)` be the graph with:
* vertices `u` and `v`;
* `n` loops at `u`;
* one loop `f` at `v`;
* `k` edges from `u` to `v`.

The convention is `s_e^*s_e=p_(r(e))`, and hereditary sets are forward
closed.  `C*(F_(n,k))` has the single nontrivial gauge-invariant ideal
`I_{v}`.  This is the circle-ideal / Kirchberg-quotient entry of the
Evington--Ng--Sims--White table, and `F_(2,1)` is its smallest model.

1. **Model.**  Let `P` consist of `v` and all words `w g_j`, where `w` is a
   word in the loops at `u`.  On `l^2(P)`, let
   `D_0=C*(1, E_v, G_j, T_i)`, where:
   * `T_i` prepends the `i`th loop and kills `delta_v`;
   * `G_j=|delta_(g_j)><delta_v|`;
   * `E_v=|delta_v><delta_v|`.

   Then `K subseteq D_0`, `D_0/K=O_n`, and

   ```text
   C*(F_(n,k)) = C(T,K) + D_0 tensor 1   inside C(T,B(l^2 P)),
   ```

   with `s_f |-> E_v tensor z`.  Under this isomorphism `I_{v}=C(T,K)`.
2. **Bound.**
   ```text
   1 <= dim_nuc(C*(F_(n,k))) <= 2.
   ```

Whether the value is one is the open ENSW entry.

## Attempts

* **Two proofs of the upper bound.**
  * The constant-symbol theorem `stw83-constant-symbol-pullback-one-extra-colour`
    applies with `X=T` and `B=O_n`.
  * Evington's full-extension theorem (arXiv:2012.03650) applies because
    `C*(F_(n,k))` is unital and `O_n` is simple.
* **The dimension-one question.**  Both schemes tried here stop at three
  colours.
  The quotient colours can be placed in the hereditary subalgebra orthogonal
  to the inner coefficient corner `M_R(C(T))`.  The transition band, however,
  meets both that corner and the outer subalgebra.  The inner corner needs
  two colours, and only one of them can be pushed off the band.  This is the
  same position as in the circle-by-circle family.  Within this scheme,
  replacing `C(T)` by `O_n` in the quotient changes only the outer colours.
  This is a heuristic colour count, not a no-go theorem.  See Section 8 of the artifact and
  `stw83-plateau-buffer-recolouring-hinge`.
* **Splitting.**  By `stw83-cuntz-circle-graph-splits-iff-k-equals-n-minus-1`,
  `F_(2,1)` is a split extension with a unital copy of `O_2`.  The splitting
  does not centralize the ideal, and it does not make the algebra
  `O_infinity`-stable, so no dimension-one argument was obtained from it.
