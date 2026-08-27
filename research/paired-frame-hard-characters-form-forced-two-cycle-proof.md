---
rg: 2
id: paired-frame-hard-characters-form-forced-two-cycle-proof
kind: route
title: Exhaust all GL4 changes preserving the symbolic wedge kernel
target: paired-frame-hard-characters-form-forced-two-cycle
requires:
  - support-packet-paired-word-frame-exposes-forbidden-rank
artifacts:
  - experiments/schur_packet_frame_transport_cycles.py
---

Represent a change of the four noncentral frame generators by a binary
`4 x 4` matrix.  The verifier enumerates all `2^16` matrices, retains the
invertible ones, applies the induced exterior-square action to the six
commutator pairs, and keeps exactly those preserving the common symbolic
relation kernel of the plus and minus frames.  There are 32.

For each retained matrix and each of the eight source central characters, the
script evaluates the pulled-back alternating form and finds its unique target
character.  The resulting 32 permutations collapse to eight distinct
patterns of multiplicity four.  Every pattern contains

```text
plus 101 -> minus 011,
plus 011 -> minus 101.
```

The search is exhaustive over the complete finite parameter space, and all
rank, kernel, uniqueness, cardinality, and hard-pair assertions are executable
assertions rather than conclusions inferred from printed output.
