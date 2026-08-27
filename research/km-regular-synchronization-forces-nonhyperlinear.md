---
rg: 2
id: km-regular-synchronization-forces-nonhyperlinear
kind: route
title: Apply regular-branch correction to the minimally almost periodic simple Kac-Moody lattice
target: non-hyperlinear-group
requires:
  - simple-kazhdan-kac-moody-lattices-exist
  - regular-branch-liftability-plus-fd-kernel-forces-nonhyperlinear
  - compact-hyperbolic-km-regular-microstates-synchronize
---

An infinite finitely generated simple group has no nontrivial
finite-dimensional unitary representation.  Indeed a nontrivial
representation is faithful by simplicity; its finitely generated linear
image is residually finite by Malcev, which would make the original infinite
simple group residually finite, impossible.  Thus every finite-dimensional
representation kills every chosen `w!=1`.

The synchronization hypothesis is exactly regular-branch liftability for
this `Gamma`.  Apply
`regular-branch-liftability-plus-fd-kernel-forces-nonhyperlinear`.

