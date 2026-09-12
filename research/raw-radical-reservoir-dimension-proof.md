---
rg: 2
id: raw-radical-reservoir-dimension-proof
kind: route
title: Compare half-spin carrier dimension with the full-spin target
target: raw-radical-full-scale-merge-needs-an-equal-reservoir
requires:
  - boolean-violation-is-one-raw-radical-qubit-drop
  - finite-graph-of-groups-representation-types-are-integer-flows
---

On the forbidden selector atom, `(BRD7)` gives four simples of dimension
`d=2^(N-1)`, while `(BRD6)` gives baseline dimension `2d`.  The raw radical
words identify the four central summands but do not change these dimensions.
For multiplicity vector `(m_chi)`, additivity of Hilbert-space dimension gives
`(RFM2)`.

Every generator in an ordinary unitary presentation acts on one fixed Hilbert
space.  HNN stable letters are unitaries, finite crossed-product generators
are unitaries, and restriction to a subgroup merely decomposes that same
space.  Hence a target subrepresentation containing `n` baseline simples has
dimension `2dn` and cannot exceed the source carrier dimension plus any
explicitly admitted reservoir.  This proves `(RFM3)` and `(RFM5)`.

For the half-spin comparison, quotient the forbidden alternating space by its
two-dimensional radical, or equivalently choose any vector-space complement
`W`.  The alternating form restricted to `W` is nondegenerate: a vector in
the radical of the restriction is orthogonal to `W` and already orthogonal to
the original radical, hence to the whole space, so it belongs to the original
radical and to `W`, and is zero.  The packet on `W` therefore has one marked
simple `sigma` of dimension `d`.  Each of the four extensions across the
radical restricts to that same `sigma` once.  A full baseline simple has twice
its dimension; if it restricts only through the common marked type, its total
multiplicity is two, while any other restriction summands are complementary
types rather than the requested carrier.  This proves that the apparent
diagonal Morita merge is exactly a scale change, not the required recurrent
reset.
