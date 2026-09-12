---
rg: 2
id: mf-kazhdan-group-without-finite-quotients-is-trivial
kind: claim
title: An operator-MF Kazhdan group with no nontrivial finite quotient is trivial
distinct_from:
  exact-kazhdan-radical-kernel-cannot-be-lef: that records the LEF case in prose, inside a mapping-torus radical target; this states the operator-MF case as a standalone claim, so that consumers outside that target can require it
  lef-implies-operator-mf: that supplies MF from local embeddings into finite groups; this uses MF, through weak quasidiagonality, to force finite quotients on Kazhdan groups
artifacts:
  - research/artifacts/operator-mf-weak-quasidiagonality-audit-2026-09-11.md
---

Let `G` be a countable group with property `(T)` that is operator MF (in the
norm-matrix-corona sense of `countable-group-mf-conventions`).  If every
homomorphism from `G` to a finite group is trivial, then `G = 1`.

Contrapositive form used by consumers: an infinite Kazhdan group with no
nontrivial finite quotient is not MF.

## Attempts

- **Via Ozawa--Thom, audited 2026-09-11.** Proposition 3.19 in Dadarlat
  assumes weak quasidiagonality, including completely positive maps on the
  full group C*-algebra. The cited MF-to-weak-quasidiagonality passage has
  not supplied that additional approximation step. The source-owned
  obstruction `mf-to-weak-qd-citation-has-unproved-lifting-step` invalidates
  the old citation route. The proven conclusion with the stronger
  hypothesis is `weak-qd-kazhdan-quotientless-group-is-trivial`.
- **Missing step.** It would suffice to prove that every operator-MF
  Kazhdan group without finite quotients admits such completely positive
  approximations, or to construct a finite quotient by a different
  argument. This claim has not been refuted by the audit.
