---
rg: 2
id: mixed-permanence-closures-collapse-proof
kind: route
title: Discharge the conditional Corollary D' with decidable simple FA hosts
target: mixed-permanence-closures-collapse-boone-higman-to-base
requires: [finitary-permanence-closures-collapse-boone-higman-to-base, decidable-groups-embed-in-decidable-simple-fa-groups]
---

Part 5 (D) of `finitary-permanence-closures-collapse-boone-higman-to-base`
states: if `decidable-groups-embed-in-decidable-simple-fa-groups` holds, then
whenever `All(C)` hosts every finitely generated group with solvable word
problem, `C` hosts every finitely generated group with solvable word problem.
The hypothesis is now established. `∎`

Unpacked (Corollary D' in `finitary-permanence-closures-collapse-proof`): a
decidable `G` lies in a finitely generated simple FA group `K` with solvable word
problem; `K` lies in a member of `All(C)`; by Proposition B there (Lemma 7:
subgroups, kernels or quotients by simplicity, coordinates by simplicity,
union terms by finite generation, vertex groups by FA), `K` lies in a member of
`C`.
