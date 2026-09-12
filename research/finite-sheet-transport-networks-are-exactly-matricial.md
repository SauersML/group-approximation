---
rg: 2
id: finite-sheet-transport-networks-are-exactly-matricial
kind: claim
title: Every finite rank-balanced sheet-transport network has an exact finite monomial model
distinct_from:
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that balances only vertex and edge representation multiplicities and leaves the intertwiner holonomy open; this starts with actual finite sheet bijections and realizes their entire monodromy exactly.
  regular-orbit-induction-coherifies-finite-edges: that stabilizes a finite orbit of group monomorphisms to make one equivariant edge; this is the coordinate-set groupoid construction for an arbitrary finite context network and separates covariance from literal shared-variable equality.
  coherent-balanced-context-permutations-would-give-a-ce-trace: that proves globally coherent gauges cannot exist for a no-CE BCS; this proves every incoherent finite gauge system is nevertheless an exact finite transport model and identifies why that is not a BCS representation.
  two-nand-triangles-have-only-free-finite-packet-indices: that checks the first two overlap types by explicit three- and six-dimensional models; this handles every finite number of S4 NAND packets and every finite incidence graph.
---

Let `Y` be any finite connected context multigraph.  At a vertex `v`, let
`Omega_v` be a finite coordinate set labelled by allowed assignments of a
Boolean predicate.  After the stipulated rank balancing, assume

```text
|Omega_v|=D                                               (FST1)
```

throughout the connected component.  For every oriented incidence edge
`e:v->w`, labelled by a shared variable `x_e`, suppose the transport data is
a bijection

```text
phi_e:Omega_v -> Omega_w,       phi_(bar e)=phi_e^(-1),  (FST2)
```

which preserves the value of `x_e`.  These data include arbitrary sheet
choices and arbitrary cycle holonomy.

Choose set identifications `i_v:Omega_v->[D]`.  On `C^D`, put the diagonal
signs

```text
X_(v,x) delta_(i_v(omega))
  =(-1)^(omega(x)) delta_(i_v(omega)),                  (FST3)
```

and let `U_e` be the permutation matrix of
`i_w phi_e i_v^(-1)`.  Then every local predicate holds exactly and

```text
U_e X_(v,x_e) U_e^*=X_(w,x_e).                          (FST4)
```

All signs and transports lie in the finite monomial group

```text
(C_2)^D semidirect S_D <= U(D).                         (FST5)
```

Thus **every** relation which merely records the prescribed local predicate
tables, sheet-bijection covariances, inverse edges, and their actual cycle
returns has an exact finite-dimensional representation.  This includes any
finite network of the standard S4 NAND packets and all of their finite
amplifications.

Fix a spanning tree and identify its fibers with one root set `Omega`.
Every chord gives a permutation of `Omega`; the cycle returns generate a
finite monodromy group

```text
H<=S_D.                                                  (FST6)
```

No flatness equation is implicit: a nonidentity element of `H` is retained
as an exact permutation matrix.  The integral sheet-identification group is

```text
Z[Omega]/<[omega]-[h omega]:h in H>
  isomorphic to Z[H backslash Omega],                   (FST7)
```

so it is free abelian.  Equivalently, for the full graph of local atom sets,
quotienting the free atom lattice by bijective edge identifications gives the
free abelian group on the resulting equivalence classes.  Pure permutation
monodromy cannot manufacture torsion.  Oriented relative atom-difference
indices may be nonzero, but they are differences inside this finite free
packet lattice and are realized by `(FST5)`.

Finite Schur/central phase lifts do not change the conclusion.  Adjoin the
finitely many diagonal roots of unity used by the local lift; together with
`S_D` they still generate a finite monomial group.  In particular every odd
NAND return `W_C=J` remains visible in exact matrices.  Products of several
such returns impose only the corresponding finite diagonal phase equation.

## Covariance is not BCS compatibility

The construction deliberately distinguishes `(FST4)` from literal equality

```text
X_(v,x)=X_(w,x).                                        (FST8)
```

Nontrivial monodromy is harmless for the transport groupoid because the
unitary `U_e` is retained.  It can prevent a choice of vertex gauges making
all copies in `(FST8)` equal.  Regular-orbit amplification records the same
finite monodromy on more sheets; it does not turn covariance into equality.

Conversely, if gauges can be chosen so that `(FST8)` holds for every shared
variable, the diagonal matrices `(FST3)` become one finite-dimensional BCS
model: every context predicate still holds and every variable has one global
operator.  For the fixed no-Connes-embeddable BCS this is impossible by
`coherent-balanced-context-permutations-would-give-a-ce-trace`.

Therefore the pure finite-transport program has an exhaustive dichotomy:

1. retain holonomy, and obtain the exact finite monomial model `(FST3)--
   (FST6)` but no compatible BCS atlas; or
2. kill/coherify holonomy, and obtain a forbidden finite-dimensional BCS
   model.

A successful common-corner construction must add a **nontransport relation**:
one not satisfied merely by choosing finite sheet bijections and retaining
their monodromy.  It must compare genuinely noncommutative block positions,
force an asymptotic collapse unavailable in the commuting model, or use an
infinite/nonamenable mechanism.  Adding more S4 packets, finite cycles, sheet
permutations, or finite central phase lifts cannot cross this boundary.

