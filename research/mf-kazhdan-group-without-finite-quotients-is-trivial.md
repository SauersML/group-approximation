---
rg: 2
id: mf-kazhdan-group-without-finite-quotients-is-trivial
kind: claim
title: An operator-MF Kazhdan group with no nontrivial finite quotient is trivial
distinct_from:
  exact-kazhdan-radical-kernel-cannot-be-lef: that records the LEF case in prose, inside a mapping-torus radical target; this states the operator-MF case as a standalone claim, so that consumers outside that target can require it
  lef-implies-operator-mf: that supplies MF from local embeddings into finite groups; this uses MF, through weak quasidiagonality, to force finite quotients on Kazhdan groups
---

Let `G` be a countable group with property `(T)` that is operator MF (in the
norm-matrix-corona sense of `countable-group-mf-conventions`).  If every
homomorphism from `G` to a finite group is trivial, then `G = 1`.

Contrapositive form used by consumers: an infinite Kazhdan group with no
nontrivial finite quotient is not MF.

Proof sketch (full text in the citation route): MF implies weakly
quasidiagonal; an infinite weakly quasidiagonal Kazhdan group has an infinite
residually finite quotient (Ozawa--Thom); that quotient has a nontrivial
finite quotient.  A nontrivial finite group is its own nontrivial finite
quotient.
