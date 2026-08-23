---
rg: 2
id: kun-thom-wreath-not-weak-mf-by-collapse
kind: route
title: A strict Kun--Thom compressor collapses two distinct commuting lamps
target: kun-thom-wreath-weak-mf
requires:
  - kun-thom-nonsofic-wreath
  - infranormal-nonnormal-has-infinite-compression-orbit
  - compression-torsion-collapse
artifacts:
  - research/artifacts/radical-renormalization-2026-08-23.md
---

The Kun--Thom hypotheses give an infranormal nonnormal Kazhdan pair
`Gamma<G`.  By `infranormal-nonnormal-has-infinite-compression-orbit`, choose
a strict compressor `s` with `s Gamma s^-1 < Gamma`.

In

```text
W=(directSum_(G/Gamma) C_2) semidirect G
```

take the nontrivial lamp `k` at `s Gamma`.  It is an involution; its
`Gamma`-orbit consists of commuting coordinate lamps; and
`s Gamma s^-1=Stab_G(s Gamma)` centralizes it.  Therefore
`compression-torsion-collapse` says every norm-matrix-corona representation
identifies `k` with every `Gamma`-conjugate.

Strictness supplies `gamma in Gamma \ s Gamma s^-1`.  Then
`gamma s Gamma != s Gamma`, so the two-lamp element
`k_(gamma s Gamma) k_(s Gamma)` is nontrivial in `W` but is killed by every
corona representation.  Hence `W` is not weak MF.  This is a negative
resolution of the target claim.
