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

2. **Rigidity search on the Houghton-like route (2026-09-18, lane bh-free-34).** *No rigidity mechanism found.*
   - **The question.** Can (T) of the input make the relations of a Houghton-like envelope finite?
   - **Where the gate sits.** The envelope's remaining gate is the near relations pinning the enumeration
     `nu` down (`free-shift-houghton-like-envelopes-are-not-fp`). These relations are between `lambda(P)` and
     the shift for the chosen finitely presented overgroup `P`, not for the input `S`.
   - **Why (T) doesn't help.** `P` can always be replaced by the non-FW overgroup `P * Z`, so a Kazhdan
     hypothesis on `S` neither helps nor hurts the gate.
   - **Landed:** `fg-simple-subgroups-of-houghton-like-groups-embed-in-germs`. Every finitely generated
     infinite simple subgroup of `H_n(G)` embeds in `G/FSym(N)`, and for free-shift envelopes every simple FA
     subgroup embeds in `P`. So the Houghton-like route passes the Kazhdan filter: its hosts keep the germ
     group's simple Kazhdan subgroups, unlike the germ-extension regime of
     `normal-germ-extensions-of-v-have-only-finite-kazhdan-subgroups`. But it creates no new ones.
