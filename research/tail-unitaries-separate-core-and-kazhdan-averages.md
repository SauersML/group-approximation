---
rg: 2
id: tail-unitaries-separate-core-and-kazhdan-averages
kind: route
title: Use finite-core tail centralizers and the internal Kazhdan gap
target: finite-leavitt-core-averages-stay-far-from-kazhdan-heat
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
  - binary-leavitt-elementary-group-is-simple
  - leavitt-center-is-coefficient-field
  - steinberg-finite-presentation-and-kazhdan-theorem
artifacts:
  - research/artifacts/leavitt-finite-core-averaging-separation-2026-09-08.md
---

At coefficient depth `d`, scalar matrices on the first `3*2^d`
coordinates commute with the repeated tail unit `I_(3*2^d) tensor q`.
The resulting group element is nonidentity and belongs to `L`. Its
canonical group unitary is fixed by averaging over `F_d`, but is
orthogonal to the `L`-conjugation invariant space in `L^2(N)`.

The elementary block centralizer calculation and infinite simplicity
identify that invariant space with `L^2(L(K))`, where
`K=diag(I_3,R^x)`. Property (T) supplies a uniform lazy averaging gap
on its orthogonal complement. Restriction to the reducing subspace
`L^2(N)` makes these statements valid in every finite extension.

Taking norms on the tail unitary gives exact distance one between the
two expectations and the quantitative bound for finite average powers.
Countable diagonalization in a tracial ultraproduct makes one unitary
commute with all fixed core elements while retaining every averaging
decay bound. Expanding the squared norm of a finite average as finitely
many literal word traces gives the finite-matrix test in the artifact.

The proof distinguishes fixed subgroups in the limiting algebra from
subgroups whose depth grows at matrix coordinates. It makes no claim
that their invariant algebras coincide.
