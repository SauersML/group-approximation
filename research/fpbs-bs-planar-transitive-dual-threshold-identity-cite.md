---
rg: 2
id: fpbs-bs-planar-transitive-dual-threshold-identity-cite
kind: route
title: Import Theorems 1.1 and 3.8 of Benjamini and Schramm on planar transitive graphs
target: fpbs-bs-planar-transitive-dual-threshold-identity
requires: []
---

Citation import, not a reproof.

I. Benjamini, O. Schramm, *Percolation in the hyperbolic plane*, J. Amer. Math.
Soc. 14 (2001), arXiv:math/9912233. The arXiv PDF (v2 text) was downloaded and
its text extracted on 2026-09-20. The quotations below are verbatim from that
text. Line breaks are rejoined and ligatures are written out.

Section 1:

> Theorem 1.1. Let G be a transitive, nonamenable, planar graph with one end.
> Then 0 < pc(G) < pu(G) < 1, for Bernoulli bond or site percolation on G.

The definitions in Section 1:

> Let pu = pu(G) be the infimum of the set of p ∈ [0, 1] such that Bernoulli(p)
> percolation on G has a unique infinite cluster a.s. The critical parameter
> pc = pc(G) is defined as the infimum of the set of p ∈ [0, 1] such that
> Bernoulli(p) percolation on G has an infinite cluster a.s.

> A transitive graph G has one end if for every finite set of vertices
> V0 ⊂ V(G) there is precisely one infinite connected component of G \ V0.

> A graph quasi-isometric with H2 must be nonamenable.

Section 2, on the dual:

> Suppose that G is an infinite connected graph with one end, properly embedded
> in X. Let G† denote the dual graph of G. We assume that G† is embedded in X
> in the standard way relative to G; that is, every vertex v† of G† lies in the
> corresponding face of G, and every edge e ∈ E(G) intersects only the dual
> edge e† ∈ E(G†), and only in one point.

Here `X = R2` or `X = H2`. Proposition 2.1 and its proof:

> Proposition 2.1. Let G be a transitive, nonamenable, planar graph with one
> end, and let Γ be the group of automorphism of G.
> (a) Γ is discrete (and hence unimodular).
> (b) G can be embedded as a graph G′ in the hyperbolic plane H2 in such a way
> that the action of Γ on G′ extends to an isometric action on H2.

> the embedding of G in the plane is unique, in the sense that in any two
> embeddings of G in the plane, the cyclic orientation of the edges going out
> of the vertices is either identical for all the vertices, or reversed for all
> the vertices.

Section 3:

> Theorem 3.8. Let G be a transitive, nonamenable, planar graph with one end.
> Then pc(G†) + pu(G) = 1 for Bernoulli bond percolation.

**How the target follows.** The identity is Theorem 3.8. The strict
inequalities are Theorem 1.1 for bond percolation. The dual is well defined
because, by the quoted uniqueness statement, any two plane embeddings have the
same face boundaries, up to a global reflection that does not change the dual
graph. The dual is locally finite with vertex degrees equal to the face sizes.
It is quasi-transitive when `G` is a Cayley graph, because the group acts on
faces with finitely many orbits. These last two facts are elementary and are
not part of the quotation.
