---
rg: 2
id: fpbs-hutchcroft-pan-tree-times-amenable-l2-threshold-is-pu-cite
kind: route
title: Import Hutchcroft--Pan's theorem that p_(2->2) = p_u on tree products with amenable Cayley graphs
target: fpbs-hutchcroft-pan-tree-times-amenable-l2-threshold-is-pu
requires: []
---

This is a citation import, not a reproof. The source is T. Hutchcroft and M.
Pan, "Dimension jump at the uniqueness threshold for percolation in
∞+d dimensions", arXiv:2412.15895v1, submitted 20 Dec 2024. It was read from
the arXiv abstract page and the HTML version on 2026-09-18.

**Theorem 1.2 (verbatim).**

> Let T be a k-regular tree for some k≥3. If G is either LL(T) or T×H for some
> infinite amenable Cayley graph H, then the critical values p_{2→2}(G) and
> p_u(G) coincide.

**Definition of the threshold (verbatim).**

> p_{2→2}:=sup{p∈[0,1]:‖T_p‖_{2→2}<∞}

The matrix is defined by

> T_p(x,y):=τ_p(x,y)

where τ_p is the two-point function.

**Definition of the product (verbatim as extracted from the HTML version;
the two slips below may be in the source or in the extraction).**

> The direct product G×H or two graphs G=(V(G),E(G)) and H=(V(H),E(H)) is
> defined to be the graph with edge set V(G)×V(H) and edge set
> {{(v,x),(v,y)}:v∈V(G),{x,y}∈E(H)}∪{{(u,x),(v,x)}:x∈V(H),{u,v}∈V(G)}

The first "edge set" should read "vertex set", and the last `V(G)` should read
`E(G)`. With those corrections this is the Cartesian product.

**Abstract (verbatim, first two sentences).**

> Consider percolation on T×Z^d, the product of a regular tree of degree k≥3
> with the hypercubic lattice Z^d. It is known that this graph has
> 0<p_c<p_u<1, so that there are non-trivial regimes in which percolation has
> 0, ∞, and 1 infinite clusters a.s., and it was proven by Schonmann (1999)
> that there are infinitely many infinite clusters a.s. at the uniqueness
> threshold p=p_u.

**Abstract (verbatim, later sentence).**

> We also prove that various other critical thresholds including the L^2
> boundedness threshold p_{2→2} coincide with p_u for such products, which are
> the first nonamenable examples proven to have this property.

This route asserts only that the cited theorem says what the target records.
