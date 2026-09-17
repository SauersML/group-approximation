---
rg: 2
id: decidable-groups-have-decidable-fa-envelopes
kind: claim
title: Every finitely generated group with solvable word problem embeds in a finitely generated group with solvable word problem and property FA
distinct_from:
  erf-groups-have-decidable-simple-kazhdan-hosts: that gives decidable Kazhdan (hence FA) hosts only for inputs with an effective residual finiteness or LEF structure; this gives a decidable FA host for every decidable input, with no approximation hypothesis and no rigidity.
  countable-group-embeds-in-fg-simple-kazhdan-group: that embeds every countable group in a finitely generated Kazhdan group with no effectivity; this keeps the word problem decidable and certifies only FA.
  boone-higman-thompson-simple-envelope: that supplies a decidable simple envelope, which need not have FA; this squares it by a swap to force FA.
  fg-perfect-wreath-c2-has-property-fa: that is the fixed-point property of one wreath square; this is the resulting universal embedding statement for decidable groups.
artifacts: [research/artifacts/decidable-fa-envelope-via-simple-wreath-square-2026-09-17.md]
---

**OPEN.** A route is drafted as an artifact but not yet fully refereed.

Let `G` be a finitely generated group with solvable word problem. Then `G`
embeds in a finitely generated group `W_G` that has:
- solvable word problem;
- Serre's property FA;
- the form `W_G = S wr C_2 = (S x S) ⋊ C_2`, with `S` an infinite finitely
  generated computably presented simple group.

## Why this matters

Property FA is the invariant that fixed-point arguments on Bass--Serre trees
see. A decidable input can always be traded for a decidable FA input containing
it. So a reduction of Boone--Higman whose only engine is permanence under
tree-like constructions (HNN extensions, amalgams, free products, graphs of
groups) must already have a base class containing every `W_G`. See
`decidable-edge-tower-premise-is-equivalent-to-boone-higman`.

## Attempts

1. **Square a decidable infinite simple envelope by a swap (2026-09-17).** See `research/artifacts/decidable-fa-envelope-via-simple-wreath-square-2026-09-17.md`. Apply `boone-higman-thompson-simple-envelope` to `G x Z`, get a decidable infinite simple `S` by Kuznetsov's argument, and take `S wr C_2`, which has FA by `fg-perfect-wreath-c2-has-property-fa`. Lens 2 of the referee panel lost its vote, so the result is recorded as an attempt, not established. Lenses 1 and 3 both returned *survives* and found no mathematical gap. Wording flag from both returned votes: "decidable" should be read as including finite generation. *Pending referee.*
