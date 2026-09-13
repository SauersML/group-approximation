---
rg: 2
id: lef-kazhdan-group-without-finite-quotients-exists
kind: claim
title: An infinite LEF Kazhdan group with no nontrivial finite quotient exists
distinct_from:
  weak-qd-kazhdan-quotientless-group-is-trivial: that proves triviality under completely positive approximations of the full group C-star algebra; this group has exact local finite models but no such approximations, so the completely positive hypothesis cannot be weakened to LEF or operator MF.
  exact-kazhdan-radical-kernel-cannot-be-lef: that node's mapping-torus statement EKL1 is not addressed here; this refutes only its printed general statement EKL2.
invalidates:
  - mf-kazhdan-without-finite-quotients-citation
  - exact-kazhdan-radical-kernel-cannot-be-lef-proof
  - non-mf-hyperbolic-from-kazhdan-quotientless
  - hyperbolic-rf-question-equals-non-mf-question-proof
  - torsion-free-kazhdan-alternating-mother-limit-gate-proof
artifacts:
  - research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md
  - research/artifacts/simple-kazhdan-lef-consequences-and-sources-2026-09-12.md
---

Let `R = LC(X,F_q) ⋊ Z` be the crossed-product ring of an infinite minimal subshift, and
`G = EL_3(R)`. Then `G` is:

- infinite and finitely generated;
- Kazhdan;
- LEF, hence operator MF;
- without nontrivial finite quotients: every homomorphism from `G` to a finite group is trivial.

Consequences:

- `mf-kazhdan-group-without-finite-quotients-is-trivial` is false.
- The general statement (EKL2) printed in `exact-kazhdan-radical-kernel-cannot-be-lef` is false: "a
  countable LEF property-(T) group with no nontrivial finite quotient is trivial".
- Granting Dadarlat's Proposition 3.19 (Ozawa--Thom: an infinite weakly quasidiagonal Kazhdan group
  has an infinite residually finite quotient), `G` is operator MF but not weakly quasidiagonal. So
  the introductory arrow "MF implies weakly quasidiagonal" in arXiv:2007.12655v2 fails for groups,
  and the missing step recorded in `mf-to-weak-qd-citation-has-unproved-lifting-step` cannot be
  supplied.

Unlike Thom's LEF non-residually-finite Kazhdan group (arXiv:0810.2180, Theorem 1.4), this one has
no finite quotient at all.
