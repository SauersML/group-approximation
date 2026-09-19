---
rg: 2
id: atlas-a4-sp6-packet-collision-screen-proof
kind: route
title: Exhaust the Sp6(2) conjugators in one internal GAP loop
target: atlas-a4-sp6-packet-collision-screen
requires:
  - atlas-shortest-a4-triangle-packet
  - atlas-word-19243-is-kernel-relation
artifacts:
  - experiments/atlas_a4_sp6_packet_scan.py
  - experiments/atlas-a4-sp6-packet-collision-scan.json
---

The replay constructs `Sp(6,2)` in Sage's GAP interface, selects all maximal
subgroups of order `40320`, and verifies that their derived subgroups have
order `20160` and are mutually conjugate.  GAP identifies the first derived
subgroup with the exact `GL(4,2)` chart used by the atlas scripts.

The script reconstructs the thirty packet words and decodes the checked JSON
word for collision `19243`.  One GAP function then loops over every
`g in Sp(6,2)`, substitutes `g h g^-1` for each factor-two chart letter, and
tests the packet before testing collision.  No floating-point calculation,
random sampling, or conjugacy heuristic occurs.  The saved JSON is the exact
output.

MSI replay: Sage 10.7 on Sioux `acn112`, one Milan CPU, 4 GiB request.  SLURM
job `16639564` completed with exit code zero in `68` seconds and peak resident
memory `1096032` KiB.
