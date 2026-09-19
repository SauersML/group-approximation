---
rg: 2
id: leavitt-heisenberg-branch-doubles-character-multiplicity-proof
kind: route
title: Translate characters by a branch-pullback kernel element and iterate
target: leavitt-heisenberg-branch-doubles-character-multiplicity
requires: []
artifacts:
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

## Direct proof

Fix the marked central-character sector and the Morita branch
`X(a) |-> X(a t_0)`.  The Heisenberg commutator law between that branch and
the transverse shear `Y(s_1)` computes the induced action on characters as a
translation `tau`.  Two facts do all the work.

1. `tau` is **nonzero**: it is read off from the commutator of the branch
   with the shear, and vanishing would force `s_1` to commute with the
   branch, contradicting `t_0 s_1 = 0` together with `t_1 s_1 = 1`.
2. `tau` lies in the **kernel of the branch pullback**: the branch is
   `a |-> a t_0`, and the translation is produced by a shear transverse to
   it, so pulling back along the branch annihilates it.

Consequently `chi` and `chi + tau` have the same image under the branch
pullback, so they sit in one branch fiber, and they are distinct because
`tau != 0`.  Branch conjugacy carries multiplicities, so both occur with
multiplicity at least `m(chi)`, and the fiber of `F chi` therefore carries
at least `2 m(chi)`.  That is `(MD)`.

Now let `chi_0` maximize `m` over the finitely many characters of an exact
finite-dimensional representation.  `(MD)` gives a character of multiplicity
at least `2 m(chi_0) > m(chi_0)`, contradicting maximality unless
`m(chi_0) = 0`.  So the marked sector is empty and the defect is killed.

No step uses property (T), a Kazhdan constant, a spectral gap, or the
commutant of the image.
