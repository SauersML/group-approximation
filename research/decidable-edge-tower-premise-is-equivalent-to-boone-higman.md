---
rg: 2
id: decidable-edge-tower-premise-is-equivalent-to-boone-higman
kind: claim
title: Tree-tower reductions of Boone--Higman collapse to their base class, and the decidable-edge tower premise is equivalent to Boone--Higman
distinct_from:
  fa-subgroups-of-graph-towers-lie-in-base-pieces: that places FA subgroups of a tower into base pieces and so covers only inputs that already have FA; this combines it with decidable FA envelopes to cover every decidable input, which upgrades "contains Boone--Higman for FA inputs" to full equivalence.
  boone-higman-iff-infinite-simple-inputs: that restricts the inputs of Boone--Higman to infinite simple groups; this shows the tower premise of the edge-tower route is itself Boone--Higman, and that tree-like permanence steps cannot reduce the problem.
  decidable-groups-embed-in-decidable-edge-towers: that is the open tower premise; this proves it is equivalent to the conjecture, so it stays open exactly as long as the conjecture does.
  compilers-cannot-drop-the-decidability-hypothesis: that shows a permanence step needs decidable edge membership; this shows that no permanence step along trees is ever used, whatever its hypotheses.
artifacts: [research/artifacts/decidable-edge-tower-premise-bh-equivalence-proof-2026-09-17.md]
---

**OPEN.** A route is drafted as an artifact but not yet fully refereed.

Say a class `C` of groups is **tree-universal for decidable groups** if every
finitely generated group with solvable word problem embeds in a graph tower, in
the sense of `fa-subgroups-of-graph-towers-lie-in-base-pieces`, whose base
groups lie in `C`. A graph tower is a finite iteration of HNN extensions and
amalgamated free products; free products and finite graphs of groups are
special cases.

**(a) Collapse to the base.** If `C` is tree-universal for decidable groups,
then every finitely generated group with solvable word problem embeds in a
member of `C`.

**(b) Equivalence.** `decidable-groups-embed-in-decidable-edge-towers` holds if
and only if `boone-higman-conjecture` holds.

**(c) Class kill.** Consider any reduction of Boone--Higman of the form
- a base class `C` of groups with finitely presented simple envelopes, together
  with
- permanence of finitely-presented-simple embeddability under HNN extensions
  or amalgams, under any side conditions on the edge groups,

applied along graph towers. Such a reduction proves the conjecture only if `C`
already contains a copy of every `S wr C_2`, with `S` a decidable infinite
simple group. By (a), it then proves the conjecture with no permanence step
at all.

The separating invariant is property FA of the envelope `W_G` of
`decidable-groups-have-decidable-fa-envelopes`. The permanence premise
`bh-embeddability-survives-decidable-edge-hnn` is never consumed on the way to
the conjecture. It remains meaningful only for hierarchies over a fixed base,
such as Magnus--Moldavanskii hierarchies of one-relator groups or towers over
free groups, which by (a) cannot be universal.

## What survives

A reduction of Boone--Higman to closure of the embeddable class under
operations must use at least one operation that is not a tree operation. It
must be able to manufacture, from pieces without FA, the FA group
`S wr C_2`. Examples are direct or graph products, wreath products, extensions,
passage to quotients, and the actor-orbit problems of twisted Brin--Thompson
groups. By (a) together with `boone-higman-iff-infinite-simple-inputs`, the
hard inputs can be taken to be the FA groups `S wr C_2` with `S` infinite,
finitely generated, computably presented and simple.

Directed unions add nothing either. `W_G` is finitely generated, so it lies in
a single term of any ascending union containing it.

## Attempts

1. **Push the decidable FA envelope into a base piece (2026-09-17).** See `research/artifacts/decidable-edge-tower-premise-bh-equivalence-proof-2026-09-17.md`. It requires `decidable-groups-have-decidable-fa-envelopes` and `fa-subgroups-of-graph-towers-lie-in-base-pieces`, and takes `B = G`, `n = 0` for the converse. Lens 2 of the referee panel lost its vote, so the result is recorded as an attempt, not established. Lenses 1 and 3 both returned *survives* and found no mathematical gap. Wording flag from both returned votes: part (c) should say that *some member* of `C` contains a copy of each `S wr C_2`, not that `C` contains every one. *Pending referee.*
