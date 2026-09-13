---
rg: 2
id: block-component-group-class-at-most-excess-plus-two
kind: claim
title: The unitary component group of Gamma(End E) over a d-dimensional complex has nilpotency class at most d − 2·rank E + 2
distinct_from:
  equal-dimension-ah-component-groups-class-two: That is the case d <= 2·rank, class at most two, proved by the gauge/Euler sequence; this bounds every excess e = d − 2·rank by e + 2 through the skeletal filtration.
  simple-ah-algebra-with-class-three-component-group: That constructs a simple algebra with class at least three; this is an upper bound for single blocks and bounded-excess limits, and it forces unbounded excess for large class.
artifacts:
  - research/artifacts/component-group-class-bound-by-excess-2026-09-12.md
---

Let X be a connected finite CW complex of dimension d and E -> X a Hermitian
bundle of rank r. Put e = d − 2r. If e >= 0, then U(Gamma(End E))/U_0 is
nilpotent of class at most e + 2. If e < 0, it is K^1(X).

Consequences:

- A unital injective inductive limit of finite sums of such blocks, all of
  excess at most e, has U(A)/U_0(A) nilpotent of class at most e + 2.
- Every such AH limit has a locally nilpotent unitary component group.
- C(T^2 x S^3, M_2) has class exactly three.
- A simple AH limit of this kind with gamma_c != 1 needs blocks of excess
  at least c − 2 cofinally.

Complete argument; not independently reviewed.
