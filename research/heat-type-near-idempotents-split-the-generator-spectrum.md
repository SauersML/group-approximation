---
rg: 2
id: heat-type-near-idempotents-split-the-generator-spectrum
kind: claim
title: A near-idempotent heat semigroup forces a diverging multiplicative gap in its generator, and is close to the low-band spectral projection
distinct_from:
  bistochastic-channel-rounding-fails: that asks for a counterexample family to unrestricted rounding; this is a structure theorem for the heat-type case, which converts the search into a question about the low spectral band of the generator and supplies no counterexample.
  near-weyl-covariant-channels-round: that rounds maps close to their own twirl over a projective group basis, a covariance hypothesis; this assumes only that the channel is a self-adjoint heat semigroup and concludes a spectral dichotomy, not rounding.
  schur-near-idempotents-round-dimension-uniformly: that rounds maps diagonal in a matrix-unit basis to expectations; this treats semigroup generators with no basis hypothesis and does not round anything.
artifacts:
  - research/artifacts/fd-compressor-commutant-and-cycle-rounding-2026-09-12.md
---

**ESTABLISHED.**

Let `A >= 0` be self-adjoint on `(M_D, ||·||_2)` with `tr` the normalized trace,
and let `Phi = exp(-tA)` be unital and trace preserving, so `Phi` is self-adjoint
for the trace inner product with spectrum in `(0,1]`. If

```text
||Phi^2 - Phi||_(2->2) <= delta < 1/4,
```

then, writing `a = -log(1-2delta)/t` and `b = log(1/(2delta))/t`,

```text
spec(Phi) is contained in (0, 2delta] ∪ [1-2delta, 1],
spec(A)   is contained in [0, a] ∪ [b, infinity),
||Phi - P||_(2->2) <= 2delta,
```

where `P` is the spectral projection of `A` onto `[0,a]`. The gap ratio
`b/a ~ log(1/(2delta))/(2delta)` diverges as `delta -> 0`.

## What this does to the merged rounding target

The heat-type case of `bistochastic-channel-rounding-fails` is now a question
about one subspace. `Phi` is within `2delta` of the orthogonal projection onto
the low band `V = ran P`, and a conditional expectation onto a `*`-subalgebra is
exactly the orthogonal projection onto that subalgebra. So:

```text
a heat-type counterexample exists
  <=>  a bistochastic generator has a low band V, separated from the rest of the
       spectrum by a diverging multiplicative gap, with V uniformly far in
       ||·||_(2->2) from every unital *-subalgebra of M_D.
```

The exact kernel is never such a `V`: `ker A` is the fixed-point set of a unital
trace-preserving CP semigroup, hence a `*`-subalgebra, and `P` is then the
conditional expectation onto it. A counterexample therefore needs eigenvalues
that are strictly positive yet a diverging factor smaller than the rest of the
spectrum, with the corresponding eigenvectors spoiling multiplicativity.

## Where the classical case goes, and why it is not recorded as proved

For a commutative generator, a weighted graph Laplacian on `D` points, the
low-band eigenvectors are the ones spectral clustering reads: `k` eigenvalues far
below the rest go with a partition into `k` weakly connected clusters, and the
span of the cluster indicators is a `*`-subalgebra. That suggests the abelian
case always rounds and that any counterexample must be essentially
noncommutative. This is a heuristic here, not a claim: making it precise needs
higher-order Cheeger inequalities with constants that are uniform in `D`, and the
usual forms lose polynomial factors in `k`. It is recorded to steer the hunt, and
it is not used by anything.
