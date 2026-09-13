---
rg: 2
id: non-ce-quantum-automorphism-group-of-finite-graph-exists
kind: claim
title: Some finite graph has a quantum automorphism group whose Haar von Neumann algebra is not Connes embeddable
artifacts:
  - research/artifacts/ex-nh-mipstar-quantum-symmetry-rung-2026-09-12.md
distinct_from:
  non-hyperlinear-group: that asks for a discrete group with non-embeddable regular trace; this asks for a Kac compact quantum group of a finite graph with non-embeddable Haar trace, which a nonhyperlinear finitely presented group implies but which is not known to imply one.
  generalized-free-wreath-hyperlinearity-permanence: that proves permanence of hyperlinear duals under Kac free wreath products; this asks for a Kac quantum group whose dual is not hyperlinear.
---

**OPEN.**  Find a finite simple graph `Z` such that `L^infinity(Qut(Z))`, the
von Neumann algebra of the Haar state on `O(Qut Z)`, admits no trace-preserving
embedding into `R^U`.  Equivalently, the discrete dual of the Kac quantum group
`Qut(Z)` is not hyperlinear.

This is the quantum-symmetry form of the goal: a symmetry of a finite object
that no finite-dimensional quantum system approximates.  It sits between the
two established endpoints.

- **Above it:** `MIP*=RE`, which gives a non-embeddable trace that no symmetry
  selects.
- **Below it:** `non-hyperlinear-group`, since a finitely presented
  nonhyperlinear group implies this claim through
  `lcs-tracial-nonru-gap-gives-qc-qa-cfi-graph-gap` and
  `qc-qa-graph-gap-gives-non-ce-quantum-automorphism-group`.

**Excluded hosts.**  The Haar algebras of `S_N^+` and `H_N^(s+)` are Connes
embeddable: their Hopf algebras are residually finite-dimensional
(Brannan--Chirvasitu--Freslon), and residual finite-dimensionality implies the
Connes embedding property (Bhattacharya--Brannan--Chirvasitu--Wang).  Both
results are as stated in Freslon's notes, Theorems 1.6 and 1.7.  A witness
`Z` therefore needs a quantum automorphism group outside those families.
