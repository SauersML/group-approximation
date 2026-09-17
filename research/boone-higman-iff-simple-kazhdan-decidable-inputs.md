---
rg: 2
id: boone-higman-iff-simple-kazhdan-decidable-inputs
kind: claim
title: Boone--Higman is equivalent to its restriction to infinite finitely generated simple Kazhdan groups with solvable word problem
distinct_from:
  boone-higman-iff-infinite-simple-inputs: that restricts the inputs to infinite computably presented simple groups, which may split as amalgams; this restricts further to simple inputs with property (T) and solvable word problem.
  simple-fa-input-boone-higman: that is the open restricted assertion for simple FA inputs; this proves that restricting to simple Kazhdan inputs, a subclass of those, loses no strength, so that claim is equivalent to the conjecture.
  fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree: that supplies the simple Kazhdan envelope; this records the resulting equivalence of embedding problems.
---

**ESTABLISHED** through `boone-higman-iff-simple-kazhdan-decidable-inputs-proof`.

The following are equivalent.

1. `boone-higman-conjecture`: every finitely generated group with solvable word
   problem embeds in a finitely presented simple group.
2. Every infinite finitely generated simple group with property (T) and solvable
   word problem embeds in a finitely presented simple group.
3. `simple-fa-input-boone-higman`: every finitely generated simple group with
   property FA and solvable word problem embeds in a finitely presented simple
   group.

So a minimal counterexample to Boone--Higman can be taken simple and Kazhdan,
with property FA: it does not split over any subgroup, it has no nontrivial
quotient, and every isometric action on a Hilbert space has a fixed point. A
proof of Boone--Higman must embed such groups, where no tree, product, union or
extension step has room.

## Attempts

1. **Envelope by the Kazhdan lamplighter host (2026-09-17).** *Settles the claim.*
