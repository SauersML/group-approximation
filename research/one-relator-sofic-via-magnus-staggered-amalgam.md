---
rg: 2
id: one-relator-sofic-via-magnus-staggered-amalgam
kind: route
title: Answer Pestov 4.9 affirmatively through the Magnus hierarchy
target: one-relator-groups-sofic
requires: [magnus-staggered-chain-sofic]
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

The classical lane, and the one that actually uses the one-relator presentation
rather than a structure theorem about it.

Take `G = <X | w>` and an epimorphism `χ : G ↠ Z`; after Nielsen moves the
`t`-exponent sum in `w` is zero, and Magnus's rewriting exhibits `K = ker χ` as a
bi-infinite iterated amalgam of shorter one-relator groups over free Magnus
subgroups.  If every such chain is sofic — the prerequisite
[[magnus-staggered-chain-sofic]] — then `K` is sofic and, since `G/K ≅ Z` is
amenable, so is `G`.

For a one-relator group with no epimorphism onto `Z` the route does not start;
but by [[nonsofic-one-relator-relator-has-primitivity-rank-two]] a counterexample
is torsion-free hence locally indicable, so it does surject onto `Z`, and the
route covers every case that matters.

## Why this is kept alongside the shell route

The two are different descriptions of the same difficulty, and neither is known
to translate into the other.  [[linton-shell-sofic]] presents it as a semidirect
product coming from the rational derived series; this presents it as an amalgam
coming from the Magnus hierarchy.  A proof through either would settle the
question, and the artifact's own recommendation is that a successful proof will
probably have to explain why the nonamenable free-edge obstruction visible here
is invisible there — so keeping both routes in the graph is not redundancy, it
is the comparison the problem is asking for.

## Where the route is already complete

On the sub-family where every Magnus overlap has rank at most one, the edge
groups are amenable, existing amalgamation/HNN permanence over amenable edge
groups applies, and the prerequisite holds.  The route is therefore not a stub:
it closes an infinite family already, and the open part is exactly
`rank C_i >= 2`.
