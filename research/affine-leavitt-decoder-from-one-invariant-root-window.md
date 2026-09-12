---
rg: 2
id: affine-leavitt-decoder-from-one-invariant-root-window
kind: route
title: Decode the active corner from Plancherel transport on one invariant root window
target: affine-leavitt-steinberg-hs-coefficient-decoder
requires:
  - steinberg-root-shear-plancherel-covariance
---

Attempt to choose one finite row-root coefficient window invariant under all
four branch multiplications, exactify its elementary abelian root table, and
read the branch operators solely from the induced permutations of its
Plancherel Fourier atoms.

This route is invalidated by
`plancherel-root-shears-have-no-compression-pressure`.  More fundamentally,
`relative-leavitt-active-subspaces-expand-by-two` says that a nonzero finite
active coefficient window cannot be invariant under both branch maps.  Any
finite construction which closes the window by adding formal boundary
coordinates makes the full shear transport stationary and loses the
coefficient boundary that was supposed to pay the active mass.
