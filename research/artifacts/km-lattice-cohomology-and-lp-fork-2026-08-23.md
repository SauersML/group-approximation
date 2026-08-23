# Kac--Moody lattices: second cohomology, end cohomology, and the LP fork (2026-08-23)

Session note accompanying the nodes `triangle-colimit-rational-h2-vanishes`,
`km-group-ring-h2-is-development-end-cohomology`,
`km-development-has-nonzero-end-cohomology-in-degree-one` and the route
`km-lp-fails-via-development-end-cohomology`.  Nothing here is a literature
import beyond the cited statements; every argument is written out in the nodes.

## What was decided

1. `H^2(Lambda;Q) = 0` for every colimit `Lambda` of a developable triangle of
   finite groups, in particular for the simple Kazhdan Kac--Moody lattices
   `Lambda_(2,4,6)(q)`.  Tool: the Cartan--Leray spectral sequence of the
   development `X` (simply connected by Bridson--Haefliger III.C.3.13), which
   needs only `H^1(X)=0`, not contractibility; the first spectral sequence
   with finite stabilizers and rational coefficients collapses to the cochains
   of the quotient triangle.  This corrects the tilt recorded in
   `compact-hyperbolic-km-lattices-fail-lp` and kills the trivial-coefficient
   clause of Ioana--Spaas--Wiersma Corollary E at every triangle colimit.

2. `H^2(Lambda; Z Lambda) = H^1_infty(X;Z) = ker(H^2_c(X) -> H^2(X))`: the
   group-ring cohomology is the degree-one end cohomology of the development.
   Corollary D therefore fires iff this end cohomology is nonzero, which is
   the new open input.

## Structure of the development (opposition complex of the twin building)

- Every 2-cell lies in exactly one twin-apartment plane; `X` is a union of
  hyperbolic `(2,4,6)` planes glued along wall segments; each edge lies in
  `q(q+1)` planes; no 2-cycle is supported in a vertex star.
- `H_2(X) != 0` UNCONDITIONALLY: for a vertex `v` of `X_+`, an `s`-panel
  `e'` of `X_-` and two generic chambers `y_i, y_j` of that panel, the
  chambers through `v` opposite to `y_i` and to `y_j` coincide (the
  opposition subgraph of the link polygon with respect to the common
  co-projection), and for any cycle `z` in it the 2-chain
  `sum eps_x [(x,y_i) - (x,y_j)]` is an embedded 2-sphere of `X` (two
  fans glued along the far-edge circle `(e_s(x), e')`).  So the development
  is never contractible, the point class of a 2-cell is never in
  `H^1_infty(X)`, and Corollary D needs a compactly supported 2-cochain
  orthogonal to all these spheres.  (An earlier draft of this note used a
  point-class argument; it is withdrawn.)

## The filtration of the twin-building product

Filter the contractible product `Z = X_+ x X_-` by minimal codistance
length.  The bottom level `X^ = Z_(<=0)` is the union of the closed product
cells over opposite chamber pairs: four-dimensional, simply connected, and
homotopy equivalent to `X` only after deleting its mixed-type 1-skeleton.
Descending faces of a chamber pair at codistance `w` are those whose
cotypes meet the descent sets `L(w)`, `R(w)`; the relative complex at each
level is a wedge over residue pairs of `(cl O_w, D)`.  With
`K = J cap wJ'w^(-1)`:

- `K = emptyset`: product of two opposition sets; relative homology only
  in degree four (opposition graphs of thick polygons connected for `q`
  large).
- `K != emptyset`: all labels of `(2,4,6)` are even, so `K = {r}` with
  `w` centralizing `r`; such levels are impossible for rank-one residues
  (wall geometry: a chamber with an edge on `M_r` cannot lie in the sector
  opposite to `c_0` at the vertex of the other two walls), so every twisted
  level is a rank-`(2,2)` pair.  There `O_w = union_(i != j) A_i x B_j`
  (classes = projections to the matched `r`-panels), the relative complex
  is the suspension of the join `A * B` minus the matched single-class
  vertex edges, and `H_3(rel) = coker(H_1(A) (x) H_1(B) -> (+) Z_1(K_(q,q)))`.
  This vanishes for the grid type (proved) and reduces to connectivity of
  explicit class graphs for `B_2`, `G_2` (`km-twisted-level-product-cycles-surject`).

Hence, if the cokernels vanish, `X^` is 2-connected, `Lambda` is of type
`F_3`, and `H^2(Lambda;Z Lambda) = H^2_c(X^) = H^3_c(Z minus X^)`: Corollary D
becomes the question whether the cusp region of the twin-building product
has compactly supported cohomology in degree three.  For affine `A~_2` the
odd labels allow rank-`(1,2)` twisted levels with nonzero relative `H_3`,
consistent with finiteness length three.

## Why this matters for the program

The LP fork is a side question (its refutation branch, LP holding, would close
the goal outright; its positive branch separates LLP from LP at the
Kac--Moody candidates).  The structural facts about the development are also
the cleanest finite-dimensional description of what a hyperlinear microstate
of `Lambda` must glue: three regular charts of the finite Levi groups along
the three edge groups, i.e. the regular microstate problem is the question
whether the two copies of `P_3` inside the virtually free tree amalgam
`P_13 *_(P_1) P_12 *_(P_2) P_23` can be made asymptotically equal in
normalized Hilbert--Schmidt norm while every word nontrivial in `Lambda`
keeps vanishing trace.
