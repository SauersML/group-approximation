---
rg: 2
id: compression-torsion-collapse-from-semisimple-packets
kind: route
title: Specialize the semisimple packet collapse to the commuting case
target: compression-torsion-collapse
requires: [semisimple-packet-multiplicity-collapse]
artifacts:
  - notes/COMPRESSION_COLLAPSE_MF_RADICAL.md
  - notes/FALSE_KAZHDAN_COMPRESSION_INDEX_TO_PHASE.md
---

## Why sufficient

[[semisimple-packet-multiplicity-collapse]] is stated for any packet whose
finite windows have images generating finite-dimensional C-star algebras of
window-bounded dimension, and concludes that a norm-corona representation
identifying `k` with its `s Lambda s^{-1}`-conjugates identifies `k` with its
whole `Lambda`-conjugation orbit.

Take the packet commuting.  Then each window algebra `A` is commutative, so
`A = C^r` and the irreducible-module multiplicity vector degenerates to the
tuple of joint spectral ranks — which is the discrete invariant
[[compression-torsion-collapse]] already runs on.  The hypotheses match term for
term: finite order of the image of `k` is the zero-dimensional-spectrum
condition, and window-bounded dimension is automatic for a commuting family of
finite-order images.  So the general statement, restricted, is this target.

## Why the specialization is worth a route rather than a remark

`compression-torsion-collapse` is already established by
`compression-torsion-collapse-fourier-route`, so this route buys the target
nothing today.  What it buys is attachment: the semisimple packet claim is the
one mechanism proposed to cover Clifford and Weyl packets, where joint spectral
projections do not exist at all and the Fourier route has nothing to say, and
without this edge that claim sits on no path to any root.  Recording it says the
right thing about the dependency — the general theorem *implies* the special one
already in hand, which is exactly the evidence a generalization owes before
anyone spends effort on it.

Anyone closing the general claim should check the specialization first: if the
commuting case does not fall out verbatim, the general statement has drifted
away from the theorem the program actually uses.
