---
rg: 2
id: steinberg-plane-transfer-stalls-at-large-primes
kind: claim
title: The single zero-plane transfer stalls at every odd prime at least seven
artifacts:
  - research/steinberg-plane-transfer-stall-proof.md
invalidates:
  - steinberg-zero-planes-via-single-transfer-orbit
distinct_from:
  steinberg-zero-plane-transfer-closes-p-five: that proves the exceptional prime-five closure; this identifies why the same rule supplies no first new plane at larger primes.
  steinberg-three-zero-families-propagate-all-chords: this refutes only iteration of the one known plane-transfer relation, not propagation using another recurrence move.
---

**ESTABLISHED FIREWALL.**  Let `Z` be the set of already-proved zero
`b`-planes.  The transfer from a known plane `B` relates the two new
candidates

```text
x=4B,                  x/(1-x)=4B/(1-4B).             (SPTS1)
```

It proves one candidate only when the other is already in `Z`; the
Möbius expression is not a freely iterable map on known planes.  Starting
with the uniform plane `Z={-1}`, the first relation has an already-known
endpoint only for `p=3`, while the exceptional `x=1` branch occurs only
for `p=5`.  Hence at every odd prime `p>=7` this closure procedure stalls
immediately at `Z={-1}`.  A second independent plane or another transfer
move is necessary for a uniform proof.

DERIVATION
steinberg-plane-transfer-stall-proof
