---
rg: 2
id: torsion-free-countable-non-mf-from-fp-witness
kind: route
title: The Fournier-Facio group is already countable and recursively presented
target: torsion-free-countable-non-mf
requires: [normal-kazhdan-defect-non-mf, fournier-facio-torsion-free-skeleton, defect-normally-generates-torsion-free-quotient]
---

## Why sufficient

The same three prerequisites that
`torsion-free-non-mf-from-normal-kazhdan-defect` uses to establish the root
produce the Fournier-Facio group `G`: torsion-free, finitely presented, and
not MF.  A finitely presented group is countable and is recursively presented,
so `G` witnesses this claim as stated, including its parenthetical preference.

No analytic step, no embedding, and no heredity lemma is consumed.  The target
is the strictly weaker existence statement and the witness is the same group.

## Why this route names the witness's prerequisites and not the root

It used to require the root claim itself, which was the natural way to write
"the established finitely presented witness is already countable".  That
created a two-claim dependency ring with
`torsion-free-fp-from-countable-witness`, which runs the other way, and the
ring was reported by `cairn check`.

An earlier version of this note explained the ring away with a false fact ---
that `cairn check` reports dependency cycles only for rings of three or more
claims.  It does not.  It suppresses a two-claim ring exactly when **both**
directions are *unary* routes, each requiring only the other claim; that is
the shape of a genuine equivalence `A <=> B`.  The reverse route here is not
unary: it also carries `torsion-free-higman-embedding` and
`mf-positive-controls`.  A route with extra prerequisites is a derivation that
happens to mention the other claim, not an equivalence arrow, so the tool was
right to report it and the ring was real.

Requiring the witness's own prerequisites instead of the root says the same
mathematical thing --- the group that establishes the root also establishes
this --- while removing the edge that closed the ring.  Nothing was demoted and
no route was deleted to achieve it.

## When a two-route ring should be kept instead

Not every such ring should be collapsed, and the difference is whether the
claims are open.

*Both claims established.*  The ring carries no information: a single witness
already satisfies both, and that witness is the honest common ancestor.
Collapsing to it, as here, loses nothing.

*Both claims open.*  The ring **is** the content --- it is the only record that
the two are one question in two coordinate systems, and removing either
direction makes one of them look like an independent open problem.  Collapsing
there would reintroduce exactly the "restatement dressed as reduction" trap the
two-route form exists to prevent.  Both other rings in this graph
(`compressed-commutant-majorana` with `kun-thom-clifford-relative-wall`, and
`leavitt-group-algebra-not-stably-finite` with
`leavitt-unit-group-algebra-not-directly-finite`) are of that second kind, are
deliberate, and say so in their own route bodies; they are correctly left
alone.

## The asymmetry that survives

This direction is unconditional.  `torsion-free-fp-from-countable-witness`
still carries `torsion-free-higman-embedding`, so it remains the route to
repair if a *different* torsion-free countable non-MF group ever needs
promoting to a finitely presented one --- which is the whole reason that route
is worth keeping rather than deleting as redundant.
