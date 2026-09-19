---
rg: 2
id: atlas-three-mode-balanced-area-sparse-collector-proof
kind: route
title: Prove the sparse balanced-area recurrence and exact Bezout ledger
target: atlas-three-mode-balanced-area-sparse-collector
requires:
  - atlas-rank-five-complete-packet-exporter
  - atlas-three-label-mode-two-unitary-moment-reduction
  - atlas-order-one-weyl-atlas-is-one-laurent-common-root-test
artifacts:
  - experiments/atlas_three_mode_balanced_area.py
  - experiments/atlas-rank5-balanced-area.json
  - experiments/atlas-rank5-balanced-area-17081560.log
  - research/artifacts/atlas-rank5-balanced-area-job-17081018.md
  - research/artifacts/atlas-rank5-balanced-area.sbatch
---

Expand each transported letter in the exact label basis `I,W,E` and normalize
the coefficient word after every multiplication to

```text
t^A S^a D^b,                 S D = t D S.
```

Terms without `E` remain affine permutations and have their normalized trace
evaluated exactly.  For a term containing `E`, cyclically rotate the trace to
its first `E` in the original projector-slot order.  Every interval between
two resets contains a single affine permutation and survives exactly when
its translation part is the identity.  Requiring all earlier projector slots
to be non-resets assigns every expansion term to one and only one first-reset
state.  Thus the sparse recurrence neither loses nor double-counts a term.
At the end, keeping precisely `a=b=0` and collecting by `A` is formula `(BAT1)`.

All arithmetic is exact.  The implementation checks five closed-form control
words before packet collection.  Its live-state cap can only abort before an
answer; it cannot change an accepted coefficient.  After Laurent shifting,
the incremental polynomial extended-gcd update maintains and rechecks the
displayed Bezout identity at every row.

The completed retry bound itself to the deterministic packet hash

```text
9e751115287b18fbe847309379d2710ffa0b1466c836d32ff4ec24446e6c2b99
```

and exited normally with sentinel `SENTINEL_ATLAS_BAT1_DONE`.  A fresh local
run reproduced the checked-in JSON byte for byte, including balanced-table
SHA-256 `bd205a6f30584f8f2edaecded6f9b98228573f3277333661118a72b05c5aeafd`.
This certifies both the sparse collector and its exact early-stop Bezout
exporter.
