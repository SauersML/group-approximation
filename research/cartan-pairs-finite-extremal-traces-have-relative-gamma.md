---
rg: 2
id: cartan-pairs-finite-extremal-traces-have-relative-gamma
kind: claim
title: Every Cartan subalgebra of a simple nuclear algebra with finitely many extremal traces has relative uniform Gamma
distinct_from:
  stw99-problem-xlix-two-cartans-relative-gamma: that root asks for one algebra containing Cartans with and without relative uniform Gamma; this theorem shows no such algebra has a finite nonempty extremal trace boundary, so it narrows the witness class without answering the root.
  stw18-finite-trace-boundary-toms-winter: that claim concerns Z-stability of the ambient algebra under strict comparison and a compact finite-dimensional boundary; this claim is about relative uniform Gamma of an arbitrary Cartan subalgebra, with no comparison hypothesis.
artifacts:
  - research/artifacts/cartan-finite-extremal-relative-gamma-2026-09-16.md
---

Let `A` be a unital, simple, separable, nuclear, infinite-dimensional
C\*-algebra. Suppose `T(A)` has finitely many extreme points, and at least
one. Let `D ⊆ A` be a Cartan subalgebra in Renault's sense.

Then `(D ⊆ A)` has uniform property Γ in the sense of
Kopsacheilis–Liao–Tikuisis–Vaccaro, arXiv:2406.09808v4, Definition 3.5.
The dividing projections can be chosen to satisfy the trace-division
identity for all `a ∈ A`. By KLTV Corollary 5.3, `(D ⊆ A)` then also has
CPoU.

The theorem covers every Cartan subalgebra: twisted ones, non-dynamical
ones, and ones whose traces do not factor through the conditional
expectation.

**Consequence for STW Problem XLIX**
(`stw99-problem-xlix-two-cartans-relative-gamma`): an algebra containing
Cartan subalgebras both with and without relative uniform Γ must have
infinitely many extremal traces. (When `T(A)` is empty, Definition 3.5 does
not apply. For `A = M_d`, no Cartan subalgebra has relative Γ.)

Remark 1 of the artifact sketches, without full proof, that relative Γ
always holds with respect to any finite set of traces. That sketch is not
part of this claim.
