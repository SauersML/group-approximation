---
rg: 2
id: pauli-support-realizes-boolean-word-calculus-proof
kind: route
title: Place Pauli X and Z on prescribed coordinate supports
target: pauli-support-realizes-boolean-word-calculus
requires:
  - corona-representations-have-an-ideal-valued-support-length
  - matrix-corona-projection-ideal-and-corner-calculus
---

Let `X,Z in U(2)` be the Pauli involutions.  Define `x_S` coordinatewise as
`X` on `S` and `1` off `S`; define `z_T` similarly with `Z`.  On
`S\T`, `x_Sz_T=X`; on `T\S`, it is `Z`; on `S intersection T`, it is `XZ`.
The active spectral ranks are respectively one, one, and two, so all are
equivalent under eventual rank domination to the support projection of
`S union T`.  This gives the product formula in `(PB1)`.

The commutator is `-1` on `S intersection T` and `1` elsewhere.  Its active
projection therefore has rank two exactly on the intersection, proving the
commutator formula.  A norm-null projection sequence is eventually zero, so
commutation is equivalent to finiteness of the intersection.

Two involutions `x_S,x_T` are conjugate only if their active spectral
projections are Murray--von Neumann equivalent.  Rank-germ classification
makes this equivalent to `S=T` modulo a finite set.  Coordinate conjugacies
give the converse, proving the conjugacy assertion.

For `(PB2)`, enumerate the nonedges of `Gamma` and partition an infinite
subset of `N` into pairwise disjoint infinite sets `C_{v,w}`, one for each
nonedge.  Add pairwise disjoint infinite private sets `P_v`.  At a coordinate
in `C_{v,w}`, let `u_v=X`, `u_w=Z`, and every other `u_a=1`; at a coordinate
in `P_v`, let only `u_v=X`; elsewhere use the identity.  Each `u_v` is a
nonidentity involution.  Edge pairs commute coordinatewise, while a nonedge
pair has commutator `-1` precisely on its assigned infinite set.  The sets
`C_{v,w}` also give the asserted almost-disjoint support ideals.
