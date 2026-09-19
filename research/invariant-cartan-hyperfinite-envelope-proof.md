---
rg: 2
id: invariant-cartan-hyperfinite-envelope-proof
kind: route
title: Apply amenability of the group algebra and functoriality of the Cartan relation
target: invariant-cartan-group-basis-needs-hyperfinite-envelope
requires: []
---

Amenability of `K` makes `L(K)` an amenable finite von Neumann algebra.  The
measured equivalence relation associated by Feldman--Moore to any Cartan
inclusion in an amenable finite algebra is amenable; by
Connes--Feldman--Weiss it is hyperfinite.

Each group automorphism of `K` induces a trace-preserving automorphism of
`L(K)`.  By hypothesis it preserves `D`; an automorphism of a Cartan pair
permutes its normalizing partial isometries and therefore sends the graph of
`S_D` to itself.  Hence the entire `Lambda`-action normalizes `S_D`.

If a source base is embedded equivariantly into `D`, restricting these Cartan
automorphisms gives the stated action inside the normalizer of the
hyperfinite relation.  When the source fills `D`, this is exactly an action
by automorphisms of `S_D`.  These implications use the Cartan placement and
make no claim about arbitrary subfactors of `L(K) rtimes Lambda`.

