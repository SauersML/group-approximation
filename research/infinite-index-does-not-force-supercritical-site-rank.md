---
rg: 2
id: infinite-index-does-not-force-supercritical-site-rank
kind: claim
title: Infinite compressor index does not force site cocycle rank beyond finite multiplicity capacity
distinct_from:
  supercritical-network-needs-noncanonical-cuts: that uses passage to an exact tracial model to rule out canonical positive-trace supercritical branching; this gives an explicit family of exact finite tensor models showing why infinite-index site recovery cannot cross the logarithmic dimension threshold.
  schur-flip-wreath-compressor-has-infinite-cocycle-rank: that constructs arbitrary fixed cocycle rank in the exact infinite-site model; this proves those fixed-rank witnesses admit perfectly exact finite truncations with enough cancellation multiplicity.
  matrix-recovery-of-schur-flip-wreath-sites: that asks for a microstate-dependent supercritical recovery theorem; this rules out deriving it from infinite index, finite-packet exactification, and scaled transport alone.
---

Consider `n` independent forbidden Schur flip squares.  Their packet
implementers have binary cocycle rank `2n`.  The tensor product of the `n`
local Pauli cancellation qubits gives an exact commuting-stable-letter model
on external multiplicity

```text
m=2^n L                                                        (ISR1)
```

for every amplification factor `L>=1`.  All packet, cross-site commutation,
and return relations for those `n` cells hold exactly, while

```text
n <= log_2 m                                                   (ISR2)
```

with an arbitrarily large gap after increasing `L`.

Letting `n` tend to infinity yields the exact infinite tensor model behind
the infinite compressor index: every fixed finite site window occurs
perfectly, yet no finite truncation contains cocycle rank above its own
multiplicity capacity.  Consequently none of the following, separately or
together, implies `n>log_2 m` in matrix microstates:

- infinite Pimsner--Popa index of the exact relative-commutant inclusion;
- recovery of every fixed number of site factors in a tracial ultraproduct;
- multiplicity-independent exactification of each fixed finite packet; or
- scaled Kazhdan transport at a preassigned rank scale.

A successful amplifier must include a **dimension-diagonal mechanism** which
observes or reacts to the residual multiplicity `L` in `(ISR1)` and activates
additional flip cells in that same model.  Ordinary compactness and fixed
window recovery cannot supply it.

