---
rg: 2
id: permutational-boone-higman-via-mif-envelopes
kind: route
title: Enlarge a finitely presented simple envelope to an MIF one and use universality of twisted Brin-Thompson groups
target: permutational-boone-higman-conjecture
requires:
  - boone-higman-conjecture
  - fp-simple-groups-embed-in-fp-simple-mif-groups
  - aut-free-groups-satisfy-permutational-boone-higman
---

Let `G` be finitely generated with solvable word problem.
1. By `boone-higman-conjecture`, `G` embeds in a finitely presented simple group `S`.
2. By `fp-simple-groups-embed-in-fp-simple-mif-groups`, `S` embeds in a finitely
   presented simple MIF group `M`.
3. By BFFHZ Corollary D, carried in `aut-free-groups-satisfy-permutational-boone-higman`,
   `M` embeds in a finitely presented simple twisted Brin--Thompson group.

The final step, from membership in such a twisted Brin--Thompson group to the
permutational statement, follows BFFHZ's own remark that a positive answer to
the MIF question makes the two conjectures equivalent. It was not re-derived
here, so treat this route as a citation of that remark.

Together with `boone-higman-via-permutational-boone-higman`, this route forms an
intended cycle: a conditional equivalence of the two conjectures under the MIF
hypothesis.
