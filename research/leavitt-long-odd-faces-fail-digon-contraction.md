---
rg: 2
id: leavitt-long-odd-faces-fail-digon-contraction
kind: claim
title: No area-eight Leavitt picture realizes the remaining odd faces of lengths eleven through fifteen
artifacts:
  - research/artifacts/verify-leavitt-long-face-digon-contractions.py
  - research/artifacts/leavitt-long-face-digon-contraction-2026-08-21.md
distinct_from:
  leavitt-long-odd-face-core-partitions: that lists the seven possible face partitions and the number of forced gate digons; this proves none contracts to a planar cubic core.
  leavitt-no-odd-nine-corner-relations: that excludes the last case by coefficient-word calculation; this exclusion is purely topological after the forced digons are recognized.
---

None of the seven face partitions in `(LOP1)` is realizable by a connected
planar cubic ribbon graph with the displayed internal digons.  Contracting
all digons produces no allowed smaller planar cubic core.

Therefore the parity-breaking area-eight residue is empty: there is no
reduced eight-cell coefficient-boundary picture whose unique odd internal
face has length `11,13`, or `15`.  Together with the exact odd relation
exclusions through length nine and the even-region closure, the three-gate
candidate has no reduced kernel picture of area eight.

