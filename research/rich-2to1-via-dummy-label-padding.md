---
rg: 2
id: rich-2to1-via-dummy-label-padding
kind: route
title: Dead -- hide the hard core in a large randomly matched dummy alphabet
target: rich-2to1-games-conjecture
requires: []
---

**Dead**, and it comes remarkably close before it fails, which is why it is
worth a node rather than a footnote.

The attack: take a hard 2-to-1 instance with left alphabet of size `K` and
embed it in a much larger alphabet whose extra labels are matched at
random.  Almost every constraint is then genuinely random, so the instance
is rich; the hard core is still there; a soundness analysis should be able
to quarantine the core, list its `K` labels, and derive a contradiction.

It is killed by `dummy-padding-cannot-beat-the-random-guessing-floor`.  A
decoder that lists the whole core and then picks a member of a 2-element
fiber succeeds at rate `2/K`.  But a 2-to-1 game with left alphabet `K`
satisfies `OPT >= 2/K` already, by independent uniform labels.  The
argument therefore reproduces the game's own random-assignment floor and
contradicts nothing, for any `K`.

The lesson is the design constraint on the entire region: richness has to
be bought with an **alphabet-independent** list of influential coordinates,
not with mostly-random constraints.  That is exactly the `|Q| <= L`,
`L` independent of `k`, in `affine-orientation-glue-lemma`.
