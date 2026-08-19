---
rg: 2
id: atlas-a4-packet-letters-generate-both-a8-charts-proof
kind: route
title: Enumerate the exact radius-five packet and close its letters under GL(4,2) multiplication
target: atlas-a4-packet-letters-generate-both-a8-charts
requires:
  - atlas-shortest-a4-triangle-packet
artifacts:
  - experiments/atlas_a4_packet_generation.py
---

The experiment reconstructs the complete radius-five spanning-tree kernel and
reselects the thirty shortest `(2,3,3)` pair-cubes using the same exact
criteria as the existing packet audit: syllable length six, X-length nine,
alternating factors, repeated letter pair, and orders `{2,3}`.

For each factor it then deduplicates every chart matrix appearing in the
packet.  There are ten distinct matrices on each side.  Starting from the
identity, breadth-first closure under right multiplication by those matrices
uses exact `4x4` arithmetic over `F_2`; no floating point or character
approximation enters.  On each factor the closure contains exactly `20160`
matrices.

The ambient group `GL(4,2)` also has order `20160`, already checked by the word
metric enumeration used to select the packet.  Hence each closure is the whole
chart group, proving `(A4-PACKET-GEN)`.