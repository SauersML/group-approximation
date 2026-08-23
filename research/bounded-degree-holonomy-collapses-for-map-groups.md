---
rg: 2
id: bounded-degree-holonomy-collapses-for-map-groups
kind: claim
title: Bounded-degree multiplicity holonomy collapses for minimally almost periodic groups
distinct_from:
  compact-hyperbolic-km-regular-microstates-synchronize: that asks for correction of arbitrary growing multiplicity holonomy on the regular branch; this proves the correction uniformly when the holonomy algebra has a fixed subhomogeneity bound.
  fixed-finite-label-km-holonomy-is-scalar-or-gapped: that treats Schur products of a fixed projective label with an arbitrary multiplicity unitary; this treats arbitrary block-diagonal holonomy, with no fixed label factor, provided every irreducible block has bounded size.
  km-su-reservoir-defeats-discrete-scalarization: that inserts a full-rank near-identity unitary in one growing multiplicity block; this proves that growing block degree is not incidental but is necessary for every surviving asymptotically flat enemy.
---

**ESTABLISHED.**  Let

```text
Gamma=<S|R>
```

be finitely presented and suppose every finite-dimensional unitary
representation of `Gamma` is trivial.  Fix `D<infinity`.  For every
`epsilon>0` there is `delta>0`, depending only on the presentation, `D`,
and `epsilon`, with the following property.

Let `A` be any finite-dimensional `D`-subhomogeneous C-star algebra and let

```text
u_s in U(A),     s in S,
```

where the trace on `A` is an arbitrary convex combination of normalized
matrix traces on its simple summands.  If

```text
max_(r in R)||r(u)-1||_2 < delta,
```

then

```text
max_(s in S)||u_s-1||_2 < epsilon.                       (BDH1)
```

Equivalently, no normalized-Hilbert--Schmidt asymptotic representation of
`Gamma` which remains inside algebras of uniformly bounded irreducible
degree can retain nontrivial holonomy.

The assertion is uniform in the number and multiplicities of the simple
summands.  Thus it is stronger than fixed ambient-dimension compactness.
Its proof is `bounded-degree-holonomy-compactness-proof`.

For the infinite simple compact-hyperbolic Kac--Moody candidate, every
finite-dimensional unitary representation is trivial.  Consequently any
enemy to `compact-hyperbolic-km-regular-microstates-synchronize` must put a
positive normalized trace mass, along a subsequence, in holonomy blocks of
unbounded matrix degree.  Repeating bounded finite labels, bounded
projective sectors, bounded matrix-unit packets, or any fixed
subhomogeneous coefficient algebra cannot support the terminal enemy.

