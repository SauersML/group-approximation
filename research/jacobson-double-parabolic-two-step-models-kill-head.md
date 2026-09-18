---
rg: 2
id: jacobson-double-parabolic-two-step-models-kill-head
kind: claim
title: In the double parabolic M_2(J) x| (EL_2(J) x EL_2(J)) of EL_4(J), every finite-dimensional two-step partial model kills the head, and in every Levi-stable filtration the head has no leading-order part
distinct_from:
  jacobson-rank-three-parabolics-are-lef: that proves the one-sided parabolic J^2 x| EL_2(J) of EL_3(J) is LEF through a two-step model that keeps the head; this proves that as soon as the right Levi is also EL_2 (block sizes 2+2), every finite-dimensional two-step model kills the head, so that model has no double-parabolic extension.
  uniform-root-kernel-invariance-kills-one-sided-defect: that kills the one-sided defect for exact additive maps that are invariant for every coefficient; this works with approximate partial models on one finite ball, finitely many coefficients and an arbitrary Levi-stable filtration, and its engine is the commutation of the left and right Levi actions on the leading symbol, not kernel invariance.
  cohn-elementary-group-is-not-lef: that proves EL_n(J) is not LEF for n >= 4 by pigeonhole plus finite presentation of St_4(J); this concerns the proper subgroup P_{2,2}, for which no finitely presented shadow is known, and kills a whole model class instead of proving non-LEF.
  binary-jacobson-el2-is-lef: that builds the mirror-glued LEF models of EL_2(J); here those models may serve as the Levi actions, and the theorem shows no finite-dimensional two-step unipotent extension of any Levi model keeps the head.
artifacts:
  - experiments/jacobson-double-parabolic-2026-09-17/check_two_step_trap.py
---

**ESTABLISHED.**

## Setting

- Let `R` be a ring with elements `s, t` such that `ts = 1`, and put `q = 1 - st`.
  The main case is `R = J = F_2<S,T | TS=1>`, where `q = Q` and `x_13(Q)` is
  the head.
- `P = P_{2,2}(R) <= EL_4(R)` is the subgroup of block matrices
  `[[A, Y], [0, B]]` with `A, B in EL_2(R)` and `Y in M_2(R)`.
- Write `n(Y) = [[1, Y], [0, 1]]`. Then `diag(A,B) n(Y) diag(A,B)^(-1) = n(A Y B^(-1))`.
- `E_ij (x) a` is the `2 x 2` matrix with `a` in place `(i,j)`, and
  `Y_a = E_11 (x) a`, so `n(Y_a) = x_13(a)`.
- `L_0 = {x_12(s), x_12(t), x_21(1), x_34(1), x_43(s), x_43(t)}`. The first
  three lie in the left Levi and the last three in the right Levi.
- `E = {0, ±1, ±s, ±t, ±st, ±q}` and `N_0 = {n(Y) : Y in M_2(E)}`. Both sets
  are finite.
- `B_* = {1} ∪ L_0 ∪ L_0^(-1) ∪ N_0` and `B_0 = B_*^3`.
- A **partial model** is a map `rho : B_0 -> GL(W)`, with `W` a
  finite-dimensional vector space over any field `K`, such that
  `rho(xy) = rho(x) rho(y)` whenever `x, y, xy in B_0`.

## Theorem (the double-parabolic trap)

Let `rho` be a partial model. Let `W = W_0 ⊃ W_1 ⊃ ... ⊃ W_m = 0` be a
filtration that is stable under `rho(L_0 ∪ N_0)`. Fix `d >= 1`, and suppose
every `n in N_0` has degree at least `d`, meaning
`(rho(n) - 1) W_k ⊂ W_(k+d)` for every `k`.

Let `eps(Y) in H_d = ⊕_k Hom(gr_k W, gr_(k+d) W)` be the degree-`d` part of
`rho(n(Y)) - 1`. Then

```text
eps(Y_q) = 0,
```

so `rho(x_13(q)) - 1` has degree at least `d + 1`.

**Two-step corollary.** Suppose `W_1 ⊂ W` is `rho(L_0)`-stable, and every
`n in N_0` satisfies `(rho(n) - 1) W ⊂ W_1` and `(rho(n) - 1) W_1 = 0`. Then
`rho(x_13(q)) = 1`.

- So no finite-dimensional two-step partial model of `P_{2,2}(J)` separates
  the head `x_13(Q)` from `1`.
- The same holds for every finite group model followed by a representation in
  which some Levi-stable subspace makes the unipotent radical two-step.

**General parabolics.** The same statement holds in every standard parabolic
of `EL_n(R)` with a unipotent-radical root `(i,k)` such that
- `i` lies in a Levi block that also contains some `j`, and
- `k` lies in a Levi block that also contains some `l`.

In that setting use `x_ij(s), x_ij(t), x_ji(1), x_kl(1), x_lk(s), x_lk(t)`
and the abelian group of block matrices supported on rows `{i,j}` and columns
`{k,l}`.

## Sharpness

Each of the three hypotheses is needed.

1. **Right Levi of size 2 (the head survives without it).** The one-sided
   parabolic `P_{2,1}(J) = J^2 x| EL_2(J) <= EL_3(J)` has two-step LEF models
   `[[Phi_M(g), ev_d(X)], [0, 1]]` that keep the head, by
   `jacobson-rank-three-parabolics-are-lef`. The left half of the proof works
   there: `Lambda(t) Lambda(s) v = v`. The step `Lambda(s) Lambda(t) v = v`
   fails, and the defect is `ev_d(Q) != 0`. The artifact computes this. What
   is missing is exactly the commuting right-Levi algebra.
2. **Finite dimension (the head survives without it).** The defining
   representation of `P_{2,2}(J)` on `J^4`, with `W_1 = J^2 ⊕ 0`, is exact,
   two-step and faithful. It is infinite-dimensional over `F_2`.
3. **Leading order only.** The theorem kills only the degree-`d` symbol of the
   head. A partial model can still keep the head in degree at least `d + 1`.
   The theorem does not say that `P_{2,2}(J)` fails to be LEF.

## Consequence

The following models of `P_{2,2}(J)` all kill the head:
- the column-evaluation model of the rank-three parabolics;
- any block-affine extension `[[Phi(A), X(Y)], [0, Psi(B)]]` with finite
  Levi models `Phi` and `Psi`, whatever they are (mirror-glued or not);
- any finite-dimensional linearization in which the unipotent radical is
  two-step on a Levi-stable flag.

So the one-sided LEF mechanism has no two-sided extension. Take any LEF model of `P_{2,2}(J)`, and any
finite-dimensional linear image of it that separates the head. Then:
- the head is invisible to the leading symbol of every `rho(L_0)`-stable
  filtration on which `N_0` has uniform degree;
- no `rho(L_0)`-stable subspace makes `N_0` two-step.

So the unipotent radical must act with Loewy length at least 3 on every
Levi-stable flag, as it does in permutation and regular-type models.

The following remain OPEN:
- whether `P_{2,2}(J)` is LEF;
- whether it is MF;
- whether it kills the head in norm-approximate models.

Two routes are left:
- models whose unipotent radical has Loewy length at least 3 and keeps the head
  in higher degree;
- a finitely presented shadow of `P_{2,2}(J)` that runs the pigeonhole argument
  of `cohn-elementary-group-is-not-lef`.

DERIVATION
jacobson-double-parabolic-two-step-trap-proof
