---
rg: 2
id: atlas-q14-index-496-exclusion-proof
kind: route
title: Close the opposite graph-parity L5(2) boundary with the dual screen
target: atlas-q14-simple-overgroup-index-is-at-least-506
requires:
  - atlas-q14-simple-overgroup-index-is-at-least-496
  - atlas-a8-index-91-to-496-reaches-standard-l5
  - atlas-a4-gl5-dual-packet-collision-screen
---

At index 496 the ambient classification forces `S=L5(2)` and puts both chart
subgroups in the standard block-diagonal conjugacy class.  The preceding
sieve has already excluded equal graph parity, so only opposite parity can
remain.  The exact dual screen applies inverse-transpose to every second-chart
label and ranges all ambient conjugators; none of its 202 packet survivors
kills `q_19243`.  Hence index 496 is impossible and the lower bound is 506.

At equality 506, the same ambient classification identifies `S=M23` and its
unique maximal `A8` class, giving the stated boundary description.

