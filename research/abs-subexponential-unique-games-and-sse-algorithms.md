---
rg: 2
id: abs-subexponential-unique-games-and-sse-algorithms
kind: claim
title: Unique games of value 1-eps^6 and regular graphs with a small set of expansion eps can be decoded in time exp(k n^O(eps)) and exp(n^O(eps^(1-beta))) (Arora--Barak--Steurer)
distinct_from:
  low-label-threshold-rank-reductions-cannot-prove-ugc: that is a polynomial-time rounding on low label-extended threshold rank instances; this is the subexponential-time algorithm on all instances, obtained by splitting by threshold rank.
  spectral-gap-no-outputs-cannot-prove-ugc: that is an SDP value bound for NO outputs with few large eigenvalues; this is an imported algorithm with no hypothesis on the spectrum.
  affine-ug-easy-on-globally-hypercontractive-graphs: that is polynomial-time on special constraint graphs for affine games; this is subexponential-time on every constraint graph and every permutation.
  unique-games-gap-admits-polynomial-time-algorithm: that is the open polynomial-time refutation form; this runs in time exp(k n^O(eps)), which is not polynomial.
---

**ESTABLISHED, BY CITATION.** Sanjeev Arora, Boaz Barak and David Steurer,
*Subexponential Algorithms for Unique Games and Related Problems*, FOCS 2010;
J. ACM 62(5), Article 42 (2015), doi `10.1145/2775105`. Credit is theirs;
nothing here is reproved. Route: `abs-subexponential-algorithms-citation`.

Verbatim (author PDF, April 8, 2010 version):

> "Theorem 5.1 (Subexponential algorithm for unique games). There is an
> exp(kn^O(ε)) poly(n)-time algorithm that on input a unique game G on n
> vertices and alphabet size k that has an assignment satisfying 1−ε^6 of its
> constraints outputs an assignment satisfying 1−O(ε log(1/ε)) of the
> constraints."

> "Theorem 2.1 (Subexponential algorithm for small-set expansion). For every
> β∈(0,1), ε>0, and δ>0, there is an exp(n^O(ε^(1−β))) poly(n)-time algorithm
> that on input a regular graph G with n vertices that has a set S of at most
> δn vertices satisfying Φ(S)⩽ε, finds a set S′ of at most δn vertices
> satisfying Φ(S)⩽O(ε^(β/3))."

> "Note that by setting β = O(1/log(1/ε)) we can get an exp(n^O(ε))-time
> algorithm that given a graph with a small set of expansion at most ε, finds
> a small set of expansion at most, say, 0.01."

Conventions, verbatim from Section 1.4 (p. 6):

* "we restrict our attention to regular undirected graphs only, though we
  allow self loops and weighted edges (as long as the sum of weights on edges
  touching every vertex is the same)";
* "We say that f(n) = exp(g(n)) if there is some constant c such that
  f(n)⩽2^(c·g(n)) for every sufficiently large n. Throughout this paper, the
  implicit constants used in O(·) notation are absolute constants,
  independent of any other parameters."

The proof of Theorem 5.1 assumes a `d`-regular constraint graph, "without loss
of generality (see Appendix A)". Appendix A reduces "distinguishing between a
1−ε vs 1−γ satisfiable unique game G to ... a 1−ε/10 vs 1−γ/10 satisfiable
unique game G′ whose constraint graph is regular". It replaces each vertex of
degree `d` by a cloud of `d` vertices joined by a constant-degree expander
that carries weight 0.9 of equality constraints. So `G′` has one vertex per
edge endpoint of `G`.

The authors draw the reduction-size consequence themselves (p. 2): "even if the
UGC is true then (assuming 3SAT has fully exponential complexity) the
corresponding reduction from 3SAT to Unique Games would have to run in
n^(1/ε^0.01) time ... in particular the UGC cannot be proved via a gadget
reduction from Label Cover". On p. 3 they add that the algorithm "really
depends on completeness parameter being close to 1". The node
`ugc-hardness-reductions-need-epsilon-dependent-size-exponent` makes that
remark precise and carries it through the BKM noise test and SSE.
