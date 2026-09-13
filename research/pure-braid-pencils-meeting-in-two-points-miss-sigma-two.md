---
rg: 2
id: pure-braid-pencils-meeting-in-two-points-miss-sigma-two
kind: claim
title: "Characters on two pencils meeting in exactly two punctures are not in Sigma^2(P_n)"
distinct_from:
  pure-braid-sunflower-characters-obstruct-bnsr-invariants: that claim covers pencils meeting in one puncture, via a split quotient; this covers pencils meeting in two punctures, where no split quotient is known and the obstruction comes from resonance.
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-pencils-2026-09-13.md
---

For `n >= 5` and 4-element `U_1, U_2 <= [n+1]` with `|U_1 ∩ U_2| = 2`, no
nonzero character in `L_{U_1} + L_{U_2}` lies in `Sigma^2(P_n)`. Example for
`n = 5`: a `P_4`-circle character on strands `{1,2,3,4}` plus a `P_3`-circle
character on strands `{3,4,5}`.

These characters lie in `Sigma^1(P_n)`: for generic parameters they are on no
KMM circle.

## Attempts

- Via resonance: `braid-arrangement-pencils-meeting-in-two-points-are-resonant`
  together with the resonance upper bound
  (`arrangement-bnsr-invariants-avoid-real-resonance`) gives this (route
  `pure-braid-pencil-pairs-miss-sigma-two-via-resonance`). It waits on an exact
  resonance certificate.
- A split quotient `P_n -> F_2 x F_2` would give a direct proof (Lemma S).
  Half-plane layering fails, because loops of the two families around the
  shared punctures must cross.
