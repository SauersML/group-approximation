---
rg: 2
id: decidable-groups-embed-in-outer-extensions-of-fp-simple-groups
kind: claim
title: Every finitely generated group with solvable word problem embeds in an extension of a finitely presented nonabelian simple group by a finitely presented group acting faithfully by outer automorphisms
distinct_from:
  boone-higman-conjecture: that asks for a finitely presented simple overgroup, which is the case Q = 1 of this statement; so that implies this.
  every-decidable-group-embeds-in-an-isolated-group: that is Cornulier--Guyot--Pitsch Question 4, which this implies through `outer-extensions-of-fp-simple-groups-are-isolated`; this is a specific sufficient condition for it.
  outer-extensions-of-fp-simple-groups-are-isolated: that is the theorem that such extensions are isolated; this is the open universality statement asking every decidable input to sit inside one.
---

**OPEN.**

**Statement.** For every finitely generated group `G` with solvable word
problem there is an extension `1 → S → I → Q → 1` with
- `S` finitely presented, simple and nonabelian,
- `Q` finitely presented,
- the conjugation homomorphism `Q → Out(S)` injective, and
- `G ≤ I`.

**Implications.**
- Boone--Higman implies this. If `G` embeds in a finitely presented simple
  group, take `S` to be that group and `Q = 1`. If `G` is finite, `S` can be a
  finite alternating group; if `G` is infinite, `S` is infinite and so
  nonabelian.
- This implies `every-decidable-group-embeds-in-an-isolated-group`, by
  `outer-extensions-of-fp-simple-groups-are-isolated`.

**Complexity.** The argument of `complexity-bounded-host-classes-are-not-universal`
does not exclude a single fixed `S` here: the quotient's word problem is an
unbounded innerness search in `S` (root Attempt 3). It does exclude a fixed
`S` with `Q ≤ Aut(S)` embedded directly (root Attempt 2).

No construction is known beyond the Boone--Higman cases.
