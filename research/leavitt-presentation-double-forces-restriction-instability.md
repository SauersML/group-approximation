---
rg: 2
id: leavitt-presentation-double-forces-restriction-instability
kind: claim
title: Shulman's weak MF of the presentation double of the simple Leavitt quotient produces exact representations of the free group that converge on the kernel in operator norm yet stay uniformly apart off it
distinct_from:
  symmetric-double-weak-mf: that is the weak MF statement for symmetric doubles of residually finite groups; this applies it to the presentation double `F *_K F` of the simple nonsofic Leavitt quotient and extracts, through the free vertex groups, an operator-norm instability of restriction to the kernel.
  normal-kernel-restriction-rigidity-for-map-free-quotients: that says exact agreement on `K` forces global agreement; this says approximate agreement does not, with no dimension-uniform modulus.
  kt-double-canonical-vertex-marginals-admit-large-amalgam-twists: that builds exact twisted vertex models for the Kun--Thom double over a non-normal Kazhdan subgroup; this concerns a normal kernel in a free group and derives the twist from weak MF rather than constructing it.
artifacts:
  - research/artifacts/hyperlinear-nonsofic-attack-notebook-2026-08-26.md
---

Let `Q = EL_4(L_(F_2)(1,2))`, finitely generated, simple
(`binary-leavitt-elementary-group-is-simple`) and nonsofic
(`universal-leavitt-el4-nonsofic`); let `q : F -> Q` be a surjection from a
finite-rank free group, `K = ker q`, and `P = F *_K F` the presentation double.

**Theorem.**  (1) `P` is weak MF (`symmetric-double-weak-mf`, `F` residually
finite).  (2) Fix `f_0 in F - K`.  There are exact unitary representations
`u_n, v_n : F -> U(d_n)` and `c > 0` such that `||u_n(k) - v_n(k)||_op -> 0`
for every fixed `k in K`, while `limsup_n ||u_n(f_0) - v_n(f_0)||_op >= c`.
(3) Equivalently, for every finite `S subset K` and `epsilon > 0` there are
`d` and exact `u, v : F -> U(d)` with `max_S ||u(k) - v(k)||_op < epsilon` and
`||u(f_0) - v(f_0)||_op >= c`: restriction to `K` is injective in every
dimension (`normal-kernel-restriction-rigidity-for-map-free-quotients`) but has
no dimension-uniform modulus of continuity in pointwise operator norm.

This is the raw material of `intertwiner-retention-makes-leavitt-quotient-hyperlinear`.
