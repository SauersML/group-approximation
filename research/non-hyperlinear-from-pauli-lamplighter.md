---
rg: 2
id: non-hyperlinear-from-pauli-lamplighter
kind: route
title: Hang the Pauli group on the cosets of a co-dense Kazhdan subgroup of a stable host
target: non-hyperlinear-group
requires:
  - stable-group-with-codense-kazhdan-subgroup
  - pauli-lamplighter-over-stable-codense-kazhdan-pair
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

Given the host pair, form the Pauli lamplighter `(PL1)`; the theorem gives
`||U(J) - I||_2 -> 0` along any tuples whose defect tends to zero, while
`J != 1`, so the canonical trace has no microstates.  This route uses no
compiler, no encoding, no area and no dimension bound; its entire cost is
the stability of the host.
