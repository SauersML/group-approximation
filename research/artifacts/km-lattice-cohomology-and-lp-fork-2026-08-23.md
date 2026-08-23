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
- If `X` is contractible then the point class of one 2-cell is a nonzero
  element of `H^1_infty(X)` and LP fails.  If `H_2(X)!=0` then, by
  transitivity on 2-cells, every 2-cell lies on a 2-cycle and the question is
  whether some compactly supported cochain is orthogonal to all 2-cycles.
- `X` contractible iff `Lambda` is of type `F_infty` (Brown's criterion).  The
  affine analogue `SL_3(F_q[t,t^(-1)])` has finiteness length three
  (Bux--Köhl--Witzel), so its development is NOT contractible: the general
  formalism cannot decide the question; it is type-dependent.

## The finite reduction

Filter `Z = X_+ x X_-` by minimal codistance length.  Descending faces of a
chamber pair at codistance `w` are those whose cotypes meet the descent sets
`L(w)`, `R(w)`.  The relative complex at each level is a wedge over residue
pairs of `(cl O_w, D)`, with `O_w` the codistance-`w` pairs in the residue
pair.  With `K = J cap wJ'w^(-1)`:

- `K = emptyset`: `O_w` is a product of two opposition sets, the relative
  complex is a smash of two suspended opposition graphs, contributing only in
  degree four (opposition graphs of thick generalized polygons are connected
  for `q` large).
- `K != emptyset` (then `K <= J cap J'`, since the simple reflections of the
  `(2,4,6)` group are pairwise non-conjugate): `O_w` is a `K`-twisted
  opposition relation; for rank-`(2,2)` pairs the relative complex is the
  suspension of the join-type complex `Omega = {alpha * beta : alpha <= e,
  beta <= e', (e,e') in O_w}` and `H_3(cl O_w, D) = H_2(Omega)`.

Hence: the development is contractible, `Lambda` is `F_infty`, and LP fails
for `C^*(Lambda)`, iff `H_2(Omega) = 0` for the finitely many twisted
opposition join complexes of rank-two residue pairs of types `A_1 x A_1`,
`B_2`, `G_2` of the `(2,4,6)` twin building.  The affine case shows some such
`H_2` is nonzero for `A_2` residues.  This is the honest remaining
computation; it is finite, explicit, and of Abramenko type.

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
