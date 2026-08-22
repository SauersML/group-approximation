---
rg: 2
id: atlas-m24-packet-collision-screen-proof
kind: route
title: Screen the eighteen M24 anti-flag cells by one packet seed fiber
target: atlas-m24-packet-survivors-share-octad-and-19243-kills-all
requires:
  - atlas-shortest-a4-triangle-packet
  - atlas-word-19243-is-kernel-relation
  - atlas-m24-a8-antiflag-cells-have-thirteen-generating-cross-cells
artifacts:
  - experiments/atlas_m24_a4_packet_screen.py
  - experiments/atlas-m24-a4-packet-screen.json
---

The replay uses the natural degree-24 Mathieu group and the canonical octad
complement from the fusion theorem.  A fixed isomorphism `GL4(2)->A`
transports the sixteen factor-oriented packet edges, collision `19243`, and
q14.  Since `N_M24(A)=A` and `Out(A8)=C2`, unchanged and inverse-transpose
second-chart labels exhaust the two relative marking parities.

For one packet edge `(x,y)`, the scanner enumerates exactly the conjugators
in the fibers over conjugates `y'` satisfying `(xy')^3=1`, using one
transporter times `C_M24(y)`.  It tests the other fifteen edges first.  Only
packet survivors are classified by their unique fixed point, unique octad,
octad intersection, and chart-intersection order; only then are collision
and q14 evaluated.  These invariants identify the eighteen cells proved by
the preceding input.  Assertions pin the seed counts, the two cells in
`(M24P-1)`, all parity totals, and `(M24P-2)`.  The hardened MSI replay used
one CPU and completed in under sixty seconds.

