---
rg: 2
id: kazhdan-hyperbolic-continuum-non-fng-maximal-kernels-proof
kind: route
title: Combine torsion-free hyperbolic Kazhdan existence with continuum many simple characteristic quotients
target: kazhdan-hyperbolic-continuum-non-fng-maximal-kernels
requires: [torsion-free-hyperbolic-kazhdan-partner-exists, fp-quotient-iff-kernel-finitely-normally-generated]
artifacts:
  - research/artifacts/kazhdan-maximal-kernel-nonnoetherianity-2026-08-30.md
---

Choose the finitely presented, torsion-free, non-elementary word-hyperbolic
Kazhdan group `H` supplied by
`torsion-free-hyperbolic-kazhdan-partner-exists`.  One primary construction
is Arzhantseva--Steenbock, *Rips construction without unique product*,
arXiv:1407.2441, Corollary 1.

Coulon--Fournier-Facio, *Infinite simple characteristic quotients*,
arXiv:2312.11684v2, Corollary 4.2 (revision dated 24 August 2026), says that
every torsion-free non-elementary hyperbolic group has continuum many pairwise
non-isomorphic infinite simple characteristic quotients with any prescribed
prime torsion spectrum.  Apply it to `H` with empty prime spectrum.  Write the
resulting quotients as

```text
H ->> Q_i = H/M_i .
```

Then every `M_i` is characteristic, every `Q_i` is infinite, simple and
torsion-free, and the `Q_i` are pairwise non-isomorphic.  Property `(T)`
passes to quotients, so every `Q_i` also has property `(T)`.  Simplicity and
nontriviality make every `M_i` a maximal proper normal subgroup of `H`.

There are only countably many finite group presentations, hence only
countably many isomorphism types of finitely presented groups.  Delete from
the continuum family those indices for which `Q_i` is finitely presented.
The remaining index set still has cardinality continuum.

For every remaining `i`, if `M_i` were finitely normally generated in the
finitely presented group `H`, adjoining those finitely many normal generators
as relators to a finite presentation of `H` would give a finite presentation
of `H/M_i`.  Equivalently this is
`fp-quotient-iff-kernel-finitely-normally-generated`.  That contradicts the
choice of `i`.  Hence continuum many of the maximal characteristic kernels
are not finitely normally generated.  Relabel this subfamily as `{M_i}`.
`\u220e`
