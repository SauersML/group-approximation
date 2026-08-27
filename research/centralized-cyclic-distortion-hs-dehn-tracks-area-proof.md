---
rg: 2
id: centralized-cyclic-distortion-hs-dehn-tracks-area-proof
kind: route
title: A doubling chain of phases with one wrap-around and a rotation across its ends
target: centralized-cyclic-distortion-hs-dehn-tracks-area
requires: []
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
  - experiments/hs_dehn_centralizer_family.py
---

The diagonal `a` with phases `2 pi 2^(-x)` and the cyclic shift `t` satisfy
the doubling relator exactly except at the wrap-around, where the phase
`2 pi 2^(-L)` is left over; the rotation `k` across the two basis vectors
whose `a`-phases differ by exactly that amount has the same defect.
Conjugating `a` by `t^n` moves the chain so that the same two vectors now
differ by `2^(n-1)` times that phase, and the two-by-two identity
`||kDk^*-D||_F = |e^(i delta)-1|` gives the ratio.  Section 7 of the
artifact; numerically reproduced by the script.
