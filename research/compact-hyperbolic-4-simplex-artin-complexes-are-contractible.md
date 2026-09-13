---
rg: 2
id: compact-hyperbolic-4-simplex-artin-complexes-are-contractible
kind: claim
title: The Artin complexes of the compact hyperbolic Coxeter 4-simplex tree diagrams are contractible
distinct_from:
  compact-hyperbolic-4-simplex-artin-groups-satisfy-k-pi-1: that is the K(π,1) conjecture for these four Artin groups; this is contractibility of their Artin complexes, which implies it.
  artin-complexes-of-4335-and-5335-are-contractible: that is the case of the two paths with end labels at least 4; this is all four diagrams.
---

For `Λ ∈ {[5,3,3,3], [4,3,3,5], [5,3,3,5], [5,3,3^{1,1}]}`, the Artin complex `Δ_Λ` is
contractible. Its vertices are the left cosets of the five maximal standard parabolic subgroups,
and a set of cosets spans a simplex when they have non-empty common intersection.

`Δ_Λ` is a 4-dimensional flag simplicial complex. The link of a vertex of type `ŝ` is the
spherical Deligne complex of `Λ − {s}`, or a join of such complexes.

Route `compact-hyperbolic-4-simplex-complexes-contractible-by-cases` splits it into
`artin-complexes-of-4335-and-5335-are-contractible`, which reduces to
`h4-deligne-complex-upward-flag-toward-5-edge`, and
`artin-complexes-of-5333-and-533-11-are-contractible`.
