---
rg: 2
id: reverse-kleene-support-profile-nonmf
kind: claim
title: A proof-triggered reverse-Kleene switch gives a finitely presented self-aware non-MF group
root: true
distinct_from:
  kazhdan-clifford-non-mf-construction: that supplies the marked non-MF seed by Kazhdan commutant transport and a Clifford witness; this wraps that seed in a proof-theoretic fixed-point presentation switch.
  hilbert-hotel-block-cover-is-unconditional: that is another unconditional algebraic non-MF construction; this is a recursion-theoretic self-aware presentation.
  threshold-free-mf-compiler-equivalence: that classifies the logical strength of the compiler interface; this records the resulting concrete self-aware non-MF endpoint.
artifacts:
  - research/artifacts/seeded-self-aware-mf-switch-2026-08-23.md
---

**ESTABLISHED (2026-08-23).**  There is an unconditional finitely presented
self-aware non-MF group obtained by

```text
marked MF-radical seed
 -> one-generator halting switch
 -> proof-search fixed point
 -> nonhalting free-product branch.
```

Start from the literal group `E` and its nontrivial invisible mark `w`.  For a
machine `e`, adjoin a free generator `s` and kill `s` exactly if `e` halts.
The fixed program searches for a proof that its own compiled copy of `w` is
trivial.  If it halted, the compiler would be in the `E` branch, where `w` is
nontrivial, a contradiction.  Hence it does not halt, so its group is
`E*Z`, and the marked word lies in the MF radical by functoriality.  The mark
is nontrivial, and the group is already finitely presented, so it is non-MF
without an additional Higman step.

This is genuine proof-theoretic self-reference, but not an independent
analytic proof of the existence of non-MF groups: the seed already contains
the obstruction.  The previous support-profile wording conflated the bare
TFM1--TFM2 semantics with a stronger seed-free implementation.  The exact
equivalence is `threshold-free-mf-compiler-equivalence`.
