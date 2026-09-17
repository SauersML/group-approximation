---
rg: 2
id: mixed-permanence-closures-collapse-boone-higman-to-base
kind: claim
title: A Boone--Higman class closed under subgroups, extensions, products, directed unions and arbitrary graphs of groups hosts every decidable group only if its base already does
distinct_from:
  finitary-permanence-closures-collapse-boone-higman-to-base: that proves the collapse for Fin(C) and Inf(C) unconditionally but for the mixed closure All(C) only on LEF inputs or conditionally; this is the unconditional mixed collapse for every decidable input.
  decidable-edge-tower-premise-is-equivalent-to-boone-higman: that collapses towers of tree steps alone through the non-simple FA square S wr C_2; this collapses every mixture of tree steps with extensions, products and unions, through simple Kazhdan probes.
  fa-subgroups-of-graph-towers-lie-in-base-pieces: that moves one FA subgroup down finite graph towers; this is the resulting class kill for all closure reductions of Boone--Higman.
  fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree: that is the probe, a decidable simple Kazhdan host of each input; this is the obstruction the probe yields.
---

**ESTABLISHED** through `mixed-permanence-closures-collapse-proof`.

Let `C` be a class of groups and `All(C)` its closure under isomorphism,
subgroups, extensions, arbitrary restricted and unrestricted direct products,
directed unions and fundamental groups of graphs of groups over arbitrary
graphs, applied in any order and any transfinite number of times (as in
`finitary-permanence-closures-collapse-boone-higman-to-base`). If every finitely
generated group with solvable word problem embeds in a member of `All(C)`, then
every finitely generated group with solvable word problem embeds in a member
of `C`.

## The obstruction

**Invariant.** The probe for a decidable input `G` is the decidable simple
Kazhdan host `H ⊇ G` of `fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree`.
It is finitely generated, simple and has property FA.

**Where every member dies.** Consider a reduction of `boone-higman-conjecture`
of the form "a base class `C` of groups with finitely presented simple envelopes,
plus permanence of finitely-presented-simple embeddability under some of the
operations above, under any side conditions". At each operation the probe `H`
passes into one input: into the kernel or the quotient of an extension
(simplicity), into one coordinate of a product (simplicity), into one term of a
union (finite generation), into a vertex group of a graph of groups (FA). So
`H`, and with it `G`, already lies in a member of `C`: every permanence step is
idle, and the base class must satisfy Boone--Higman by itself.

This removes the survivor "tree steps mixed with infinitary steps, for non-LEF
inputs" from the "What survives" list of
`finitary-permanence-closures-collapse-boone-higman-to-base`. What survives:
quotient-type steps (every group is a quotient of a free group), and compilers
that are not closure operations under these constructions.

## Attempts

1. **Feed Corollary D' with the Kazhdan lamplighter host (2026-09-17).** *Settles the claim.*
