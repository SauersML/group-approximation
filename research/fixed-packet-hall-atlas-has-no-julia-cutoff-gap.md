---
rg: 2
id: fixed-packet-hall-atlas-has-no-julia-cutoff-gap
kind: claim
title: A fixed rational packet Hall atlas cannot authenticate the Julia cutoff only in matrices
distinct_from:
  atlas-a4-context-types-live-in-fixed-rational-polytope: that proves the rational-polytope description for one A4 context atlas; this applies the same integer-flow geometry to cutoff rank authentication and Hall inequalities.
  fixed-packet-julia-calculus-is-tracially-functorial: that treats C-star operations natural on the full multiplicity algebra; this treats the apparently nonfunctorial use of integer multiplicities and finite Hall matchings.
  determinant-index-cannot-authenticate-julia-heat-overlap: that rules out scalar finite-dimensional invariants; this rules out every fixed finite system of packet restriction and capacity equations.
---

Fix a finite diagram of finite packet groups, packet inclusions and finitely
many named spectral/cutoff atoms.  Suppose a proposed authentication uses
only

- irreducible multiplicities at the packet vertices;
- restriction/incidence equations between the vertices;
- ranks of the named atoms inside those types; and
- Hall matching inequalities in one fixed finite bipartite incidence graph.

Then it cannot prove a normalized rank inequality in matrices which fails
for a finite tracial multiplicity profile.

Indeed collect all irreducible and atom multiplicities into
`x in R_+^N`.  Compatibility has the form

```text
A x=0,                                                (RPH1)
```

for one integral matrix `A`; normalization is one rational affine equation.
The resulting set

```text
K={x>=0: Ax=0, dimension(x)=1}                        (RPH2)
```

is a rational polytope.  Matrix representations give its rational points,
after division by total dimension, and every rational point is realized
after clearing denominators.  Finite tracial packet decompositions give
arbitrary real points of the same polytope: ordinary integer multiplicity is
replaced by Murray--von Neumann dimension in the multiplicity algebra.

Every rank comparison and every capacitated Hall condition is a finite list
of rational linear inequalities

```text
ell_j(x)>=0.                                          (RPH3)
```

Rational points are dense in each rational face of `K`.  Therefore `(RPH3)`
holds on all integer matrix profiles if and only if it holds on all of `K`.
Equivalently, if a regular tracial profile violates the desired matching,
rational profiles violate it too and clearing denominators gives arbitrarily
large exact matrix multiplicity counterprofiles with the same normalized
violation.

Applied to `julia-authenticated-high-spectrum-rank-selector`, no fixed finite
packet/conductor library can force

```text
rank(P)<=rank(1_[alpha,1](E Q_B E))                  (RPH4)
```

solely from type restrictions and a fixed Hall graph while allowing `(RPH4)`
to fail in the regular finite tracial representation.  Integer multiplicity
does not leave a positive normalized gap: after amplification its lattice is
dense in the real multiplicity cone.

This no-go is deliberately scoped.  It does not rule out an atlas whose
size grows with matrix dimension, an unbounded conductor/first-hit family,
a nonlinear group-global correlation not determined by type ranks, or a
dimension oracle activating a new constraint.  It proves that the word
“finite-coordinate” cannot mean one fixed semisimple packet atlas plus Hall
rounding.
