---
rg: 2
id: boone-higman-from-simple-fa-inputs
kind: route
title: Pass through a decidable simple FA envelope and then upgrade it to a finitely presented simple group
target: boone-higman-conjecture
requires: [decidable-groups-embed-in-decidable-simple-fa-groups, simple-fa-input-boone-higman]
---

Let `G` be a finitely generated group with solvable word problem.

1. By `decidable-groups-embed-in-decidable-simple-fa-groups`, `G` embeds in a
   finitely generated simple group `S` with property FA and solvable word
   problem.
2. By `simple-fa-input-boone-higman`, `S` embeds in a finitely presented
   simple group `H`.

The composite embedding `G <= S <= H` is the conclusion of
`boone-higman-conjecture`.
