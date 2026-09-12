---
rg: 2
id: tensor-closed-fourier-blocks-round-central-markov-kernels
kind: route
title: Translation averaging and tensor closure turn the high Fourier blocks into a normal quotient
target: central-markov-near-idempotents-round-to-normal-cosets
requires: []
artifacts:
  - research/artifacts/central-convolution-markov-rounding-2026-09-08.md
---

The commutative little-Grothendieck theorem, in its complex form
with constant `2/sqrt(pi)`, gives a probability weight dominating
any map from `C(G)` to a Hilbert space. Apply it to `T=K^2-K`
and average the weight over right translations. Equivariance
turns that weight into the uniform measure, proving

```text
||K^2-K||_(2->2) <= (2/sqrt(pi))*delta =: epsilon.
```

Centrality makes the Fourier block on each irreducible
representation a real scalar `lambda_pi`. At `epsilon<1/10`,
each scalar is within `2epsilon` of zero or one. The high
irreducibles are closed under duals. For two high irreducibles,
the averaged squared displacement of every vector in their
tensor product is at most `16epsilon`. Each constituent thus
has scalar at least `1-8epsilon>2epsilon` and is also high.

Their matrix coefficients consequently form a unital
conjugation-closed algebra of functions, invariant under both
translations. Its level sets are the cosets of a normal
subgroup. The high spectral projection is exactly the
conditional expectation onto that algebra, and its distance
from `K` in `2->2` norm is at most `2epsilon`.

In the abelian case the characters are bounded eigenvectors
of normalized `L^2` norm one. They directly give
`||K^2-K||_(2->2)=delta`, removing the Grothendieck factor.
The diagonal matrix realization preserves both mixed norms
exactly and identifies the resulting matrix-algebra expectation.

The only imported analytic estimate is the commutative
little-Grothendieck theorem, stated with its constant in
[Kalenda--Peralta--Pfitzner, Theorem A](https://arxiv.org/html/2002.12273).
The artifact gives the remaining argument in full.
