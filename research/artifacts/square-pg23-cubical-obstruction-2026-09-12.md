# The PG(2,3) square candidate is impossible

Checked against primary literature on 2026-09-12. This closes the specific
open claim `square-pg23-kazhdan-hyperbolic-complex-exists` by refutation.
It does not settle the existence of flexibly HS-stable hyperbolic Kazhdan
groups or Gromov's residual-finiteness question.

## Precise theorem and geometric proof

Let `K` be a finite connected square complex, with `|V(K)| >= 2`, and
suppose every vertex link is the incidence graph `L` of `PG(2,3)`.
Then `π_1(K)` is not Kazhdan.

The graph `L` has 26 vertices and 52 edges, is simple and bipartite, and
has girth six. Forget the hyperbolic metric proposed in the candidate:
assign the Euclidean unit-square metric to each face. The attaching
maps remain isometries on edges. Every link cycle now has length at
least `6(π/2)`, in particular at least `2π`. Equivalently, each link is
a flag one-dimensional simplicial complex. Hence the new metric is
locally CAT(0) and its universal cover `X` is a CAT(0) cube complex.
This is a change of metric on the same complex, not a change of group.

The deck action of `Γ = π_1(K)` on `X` is cellular and free. Theorem B
of Niblo--Reeves says that every cellular action of a Kazhdan group on
a finite-dimensional CAT(0) cube complex has a global fixed point.
Applied here, that would force every deck transformation to be the
identity, so `Γ = 1`.

The combinatorial count rules that out. An edge has two ends, so
`2|E| = 26|V|`. Each square has four corners, so `4|F| = 52|V|`.
Consequently

```text
χ(K) = |V| - 13|V| + 13|V| = |V| >= 2.
```

If `Γ` were trivial, `K = X` would be contractible and would have Euler
characteristic one. Contradiction. This also shows the argument does
not depend on a conjecture about residual finiteness or hyperlinearity.

In fact the same hypotheses give an infinite fundamental group:
a finite deck group acting on complete CAT(0) `X` has a fixed point,
so would be trivial, which was just excluded.

## Exact location of the spectral mistake

The normalized adjacency spectrum of `L` is

```text
1, sqrt(3)/4, -sqrt(3)/4, -1,
```

with multiplicities `1, 12, 12, 1`. To verify this without a numerical
calculation, let `M` be the 13-by-13 point-line incidence matrix. Each
point lies on four lines and two distinct points share one line, so
`MM* = 3I + J`. Thus the singular values of `M` are four once and
`sqrt(3)` twelve times; the adjacency matrix of `L` has blocks `0,M`
and `M*,0`, and normalization divides by four.

Although `λ_1(L) = 1 - sqrt(3)/4 > 1/2`, the usual two-dimensional
simplicial link criterion cannot be applied directly to square cells.
Here is what happens in a concrete triangular subdivision.

Cone every square boundary to a new vertex at its center, creating four
triangles. At each original vertex a former square corner has become
two triangle corners, so its link is the graph `S(L)` obtained by
subdividing each edge of `L` once. Let `B` be the unsigned vertex-edge
incidence matrix of `L`. Original vertices of `S(L)` have degree four;
new subdivision vertices have degree two. Its normalized adjacency is

```text
N = [ 0       B/sqrt(8) ]
    [ B*/sqrt(8)      0 ].
```

Since `BB* = 4I + A_L`, the upper-left block of `N^2` is

```text
(4I + A_L)/8 = (I + A_L/4)/2.
```

The positive eigenvalues of `N` are therefore
`sqrt((1+λ)/2)` for the corresponding original normalized adjacency
eigenvalues `λ`. There are also zero eigenvalues from the rectangular
incidence matrix; they do not change the second largest eigenvalue.
The graph is connected, so its largest eigenvalue one is simple, and
the second largest is

```text
sqrt((1 + sqrt(3)/4)/2) = sqrt((4 + sqrt(3))/8).
```

This gives the claimed normalized Laplacian gap. It is strictly below
one half: its subtracted square root exceeds `sqrt(4/8) > 1/2`.
The new square-center links are four-cycles and have gap one, but the
old-vertex links fail the required threshold. The calculation explains
why merely triangulating the example cannot repair the purported
application of the simplicial criterion.

## Cairn consequences and provenance

The old existence claim is false, not just unsupported by its suggested
literature. Its `refuted_by` edge points to the new non-Kazhdan claim.
The general Euler-characteristic theorem remains valid; only its
suggestion that a Kazhdan square instance might exist is withdrawn.
Density-model random groups remain a separate candidate family and
are unaffected by this cubical obstruction.

This argument is a targeted application of known theory. No novelty
claim is made for the underlying fixed-point theorem or incidence
spectrum; there is no computational certificate or unperformed search.

Primary source:

- Graham Niblo and Lawrence Reeves, *Groups acting on CAT(0) cube
  complexes*, Geometry & Topology 1 (1997), 1--7,
  [author preprint](https://arxiv.org/pdf/math/9702231), Theorem B on
  printed page 3; the cubical link condition is stated on printed pages
  4--5. [Journal DOI](https://doi.org/10.2140/gt.1997.1.1).
