---
rg: 2
id: amenable-edge-graph-corner-proof
kind: route
title: Build the graph by embeddable amalgams and HNN extensions
target: amenable-edge-graph-corners-cannot-groupify-a-nonce-game
requires:
  - hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower
  - amenable-edge-hnn-preserves-hyperlinearity
---

Choose a maximal tree in the finite underlying graph.  Starting with one
vertex group, attach the other vertex groups along the tree edges.  At each
step the new group is an amalgamated free product

```text
G_old *_(G_e) G_v.                                       (AEG3)
```

The group von Neumann algebra of `(AEG3)` is the tracial amalgamated free
product over `L(G_e)`.  Since `G_e` is amenable, `L(G_e)` is hyperfinite.
Brown--Dykema--Jung permanence says that an amalgamated free product of
Connes-embeddable finite von Neumann algebras over a hyperfinite subalgebra is
Connes embeddable.  Thus every tree-stage group is hyperlinear.

Each edge outside the maximal tree adds one HNN stable letter identifying
the two images of its amenable edge group.  Apply
`amenable-edge-hnn-preserves-hyperlinearity` at every such step.  There are
only finitely many steps, proving `(AEG1)`.

If `(AEG2)` existed, faithfulness of the canonical group trace would give
`tau_Pi(q)>0`.  Hyperlinearity embeds `(L(Pi),tau_Pi)` trace preservingly into
a tracial matrix ultraproduct.  Compression by `q`, normalization by
`tau_Pi(q)`, and pullback through `Phi` produce a Connes-embeddable tracial
state of `B`, contradicting its hypothesis.

