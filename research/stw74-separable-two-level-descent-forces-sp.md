---
rg: 2
id: stw74-separable-two-level-descent-forces-sp
kind: route
title: Separable level-two descent forces property SP through separable subcounterexamples
target: stw74-hypothesis-forces-property-sp
requires:
  - stw74-separable-two-level-projection-descent
  - stw74-lxxiv-hinge-is-two-level-descent
  - stw74-counterexamples-have-separable-subcounterexamples
artifacts:
  - research/artifacts/stw74-two-level-descent-2026-09-16.md
---

Let `A` be a unital simple C\*-algebra in which every nonzero projection is
infinite, and suppose `A` fails (SP).  Choose `0!=a in A_+` such that
`Her_A(a)` contains no nonzero projection.

The separable-subcounterexample claim with `S={a}` gives a separable unital
C\*-subalgebra `C` of `A`, containing `a`, which is simple and in which every
nonzero projection is infinite; moreover `Her_C(a)` is nonzero and has no
nonzero projection, so `C` fails (SP).

The two-level-descent equivalence applied to `C` (implication (2)=>(1),
contrapositive) gives a hereditary C\*-subalgebra `H` of `C` with no nonzero
projection such that `M_2(H)` contains a nonzero projection.  This
contradicts the first required claim for `B=C`.  Hence `A` has (SP).

See Section 5 of the artifact.
