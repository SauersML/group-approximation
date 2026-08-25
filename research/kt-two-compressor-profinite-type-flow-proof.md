---
rg: 2
id: kt-two-compressor-profinite-type-flow-proof
kind: route
title: Finite quotient blindness turns both strict compressors into automorphisms
target: kt-two-compressor-irrep-flow-has-profinite-stationary-points
requires:
  - kun-thom-nonsofic-wreath
  - kt-two-positive-compressors-generate-full-obstruction
  - kt-kazhdan-polar-compressor-rounding-is-directional
  - kt-elementary-kazhdan-packet-rounds-base-lamp
---

Choose the finite quotient `q` by residual finiteness of `G`, taking a product
of finitely many quotients if necessary.  Since
`A Gamma A^(-1) subset Gamma`, conjugation by `q(A)` maps the finite group
`S=q(Gamma)` injectively into itself.  It is therefore onto.  The same proof
applies to `B`, giving `(KTF1)`.

The regular representation of a finite group is invariant up to unitary
equivalence under every automorphism.  Its character is zero off the identity,
so the choice of `q` gives the asserted canonical trace on the prescribed
window.  The regular decomposition

```text
lambda_S = direct_sum_(tau in S-hat) dim(tau) tau
```

gives `(KTF2)`, and automorphisms permute irreducibles without changing their
dimensions.  Both compressor boundary terms therefore vanish exactly.

For the structural qualification, precomposition of an irreducible
representation with an injective non-surjective endomorphism is restriction
to a proper isomorphic subgroup and can decompose.  Thus the general flow is
described by the nonnegative branching coefficients

```text
N_alpha(sigma,tau)=mult(sigma, tau after alpha),
```

not a free-semigroup action on a set.  Finally Schur decomposition identifies
`pi(Gamma)'` with the direct sum of the multiplicity matrix algebras.  The
weight vector records their sizes but no conjugation data on them.  This
proves that a scalar type-flow estimate cannot see the marked lamp condition.
