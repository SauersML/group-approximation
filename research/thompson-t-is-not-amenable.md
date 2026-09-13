---
rg: 2
id: thompson-t-is-not-amenable
kind: claim
title: Thompson's group T is not amenable
distinct_from:
  thompson-f-is-not-amenable: that is the open non-amenability problem for the subgroup F of interval homeomorphisms; this is the elementary non-amenability of the circle group T, which contains F.
---

**ESTABLISHED** through `thompson-t-is-not-amenable-proof`.

Richard Thompson's group T, the group of orientation-preserving piecewise-linear
homeomorphisms of the circle `R/Z` with finitely many breakpoints, all at dyadic
rationals, with slopes powers of 2 and mapping dyadic rationals to dyadic
rationals (Cannon–Floyd–Parry), is not amenable.

The proof uses only the invariant-measure characterization of amenability and
the fact that T contains all rotations by dyadic angles; it does not use free
subgroups.

**Use in the graph.** It is the input that makes the quasi-isometry question
"is F quasi-isometric to T?" (`thompson-f-qi-to-thompson-t-resolved`) reduce to
amenability of F: see `thompson-f-not-qi-to-t-if-f-is-amenable` and
`thompson-f-nonamenable-if-qi-to-thompson-t`.
