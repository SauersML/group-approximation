---
rg: 2
id: nonmonomial-multiplicity-obstructs-hs-compressor-transport
kind: claim
title: Nonmonomial multiplicity obstructs compressor transport even for exact representations
distinct_from:
  hs-expander-block-decomposition: That asks for a positive normalized-HS block decomposition; this gives an exact finite-dimensional counterexample to its compressor-transport clause under the general subgroup/compressor quantifiers currently written there.
  rank-one-lift-perturbation-gap-no-go: That is a finite-level spectral-gap obstruction caused by a vanishing-rank perturbation; this obstruction has zero approximation error, fixed dimension, and comes solely from nonmonomial compressor action on multiplicity space.
---

There exist infinite finitely generated property `(T)` groups
`Gamma <= G`, generators `t_1,...,t_m` with

```text
G=<Gamma,t_1,...,t_m>,
t_i Gamma t_i^(-1)=Gamma,
```

and a genuine representation `pi:G -> U(3)` for which no decomposition of
`1` can simultaneously have

1. a positive scalar adjoint Poincare gap on every `Gamma`-block, and
2. exact permutation transport of those blocks by every `pi(t_i)`.

More strongly, this rules out an **asymptotic** version with errors tending to
zero for the same exact representation: there is no function
`eps(delta)->0` such that for every `delta>0` the representation `pi`, viewed
as a `delta`-almost representation, admits a projection `p` with
`tau(1-p)<=eps(delta)`, fine blocks of positive scalar `Gamma`-gap, and
compressor drift at most `eps(delta)` to single fine blocks.

One example is

```text
Gamma = SL_3(Z),
G = Gamma x A_5,
pi(g,a) = sigma(a),
```

where `sigma:A_5 -> U(3)` is the irreducible icosahedral representation and
the compressors are lifts of a finite generating set of `A_5`.

Thus the compressor clause in `hs-expander-block-decomposition` is not a
formal consequence of property `(T)`, almost multiplicativity, or even exact
multiplicativity.  It is an additional **monomiality/coordinate-algebra**
input.  This is precisely what the permutation model has for free: its
component algebra comes from a set on which every ambient permutation already
acts monomially.
