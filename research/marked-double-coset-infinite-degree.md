---
rg: 2
id: marked-double-coset-infinite-degree
kind: claim
title: The marked double coset of the Laurent Kun--Thom pair has infinite degree
distinct_from:
  invariant-graph-crossed-product-ce: that asks for Connes embeddability of one member of the invariant-graph family; this is a group-theoretic index computation about the underlying G-set, and it deletes the finite-degree part of that family's search space.
  invariant-graph-clifford-phase: that classifies which invariant graphs keep the marked word alive; this measures the degree of the smallest such graph and finds it infinite.
  two-point-orbit-approximation: that is an approximation property of the G-set (a two-element-window weakening of a sofic action, with maps into finite symmetric groups); this is an exact index computation, [Gamma : Gamma cap h Gamma h^(-1)] infinite, with no approximation notion in it.
artifacts:
  - notes/COMMUTING_WREATH_SOFIC_RADICAL.md
---

Let `r,d>=3`, `R_+=F_q[x_1,...,x_d]`, `R=F_q[x_1^(±1),...,x_d^(±1)]`,
`Gamma=EL_r(R_+)` and `G=EL_r(R) semidirect SL_d(Z)` be the Kun--Thom
Theorem E pair, and `X=G/Gamma`.

1. **Necessary condition for a finite double coset.**  For `h in GL_r(R)`,
   if `[Gamma : Gamma cap h Gamma h^(-1)]` is finite then

   ```text
   (h^(-1))_(p i) h_(j q) in R_+   for all p,q and all i != j.
   ```

2. **The marked element fails it.**  For `h=e_12(x^m)` with `m` not in
   `N^d` — in particular for the recorded marked element
   `h=e_12((x_1...x_d)^(-1))` of notes/COMMUTING_WREATH_SOFIC_RADICAL.md,
   Corollary 2 — one has `(h^(-1))_(12) h_(11) = -x^m` outside `R_+`.
   Hence

   ```text
   [Gamma : Gamma cap h Gamma h^(-1)] = infinity,
   ```

   so the `Gamma`-orbit of the marked coset `h Gamma` in `X` is infinite and
   the orbital graph of `Gamma h Gamma` has infinite degree at every vertex.
2'. **The neighbour set has coordinates (2026-08-18).**  The infinitude of
   step 2 is now explicit: for every `p != q` the marked neighbours
   `e_(qp)(a) h_(pq) Gamma` of the base point are indexed injectively by
   `a in R_+/m^2 R_+`, because
   `U_(qp) cap Gamma cap h_(pq) Gamma h_(pq)^(-1) = {e_(qp)(a) : a in m^2 R_+}`
   exactly (`minimal-marked-graph-private-neighbour`, item 2).  That chart is
   what makes the separation argument of that claim possible, and it turns
   further demands on a neighbour into conditions on a Laurent parameter.
3. **Consequence for the invariant-graph family.**  A `G`-invariant graph on
   `X` that contains the marked edge contains the whole orbital graph of
   `Gamma h Gamma`, so **no finite-degree `G`-invariant graph on `X` keeps
   the marked word alive**.  The finite-degree, bounded-anticommutation
   regime of `invariant-graph-crossed-product-ce` is therefore empty, and
   the freedom in that family is not freedom in the direction of locality.
4. **The fixed set is nevertheless infinite, and its compressor translates
   are computable.**  `X^Gamma = {y Gamma : y^(-1) Gamma y <= Gamma}` is
   exactly `P_Gamma^(-1) Gamma / Gamma`, the coset set of the inverse
   compression semigroup, and it contains the whole ray `t^(-n) Gamma`
   because a strict compressor has no power in `Gamma` (the formalized
   `ray-injectivity`).  More generally, for every `s in G`,

   ```text
   X^(s Gamma s^(-1)) = s * X^Gamma,
   ```

   and for `s=t` a compressor this contains `X^Gamma` and contains
   `t Gamma`, which is not in `X^Gamma`.  So the `Gamma`-fixed structure of
   `X` is infinite and grows strictly along the compressor, while the marked
   orbit is infinite: the model has no finite `Gamma`-invariant coordinates
   anywhere near the mark.
