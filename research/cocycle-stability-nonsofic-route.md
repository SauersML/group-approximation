---
rg: 2
id: cocycle-stability-nonsofic-route
kind: route
title: Build a nonsofic hyperbolic group from cocycle stability of random complexes
target: nonsofic-hyperbolic-group
requires: [random-complex-linear-cocycle-stability]
---

Chapman--Peled, *Cocycle stability in permutations of random simplicial
complexes*, arXiv:2509.21566, prove the implication

> if, in a middle triangle density range, random 2-dimensional
> Linial--Meshulam complexes typically have a linear cocycle stability rate,
> then there exists a nonsofic hyperbolic group.

The implication is theirs and is proved; only its hypothesis is open, which
is why this route reduces to the single claim it requires.  Their method is
modelled on the non-local-testability of Sipser--Spielman expander codes.

This is the reason the route is worth recording here rather than only in
`notes/`: the obstruction is imported from coding theory, not from the
expander decomposition of sofic approximations of property-(T) groups.  The
no-gos catalogued in `notes/OBSTRUCTIONS.md` are all attacks on the latter,
so none of them evidently applies to whatever group this route produces.
