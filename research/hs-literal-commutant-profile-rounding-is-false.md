---
rg: 2
id: hs-literal-commutant-profile-rounding-is-false
kind: claim
title: Almost-central projections need not round to central projections of the literal commutant of an almost representation
distinct_from:
  hs-normalization-profile-rounding-crux: that is the rounding lemma whose target is the center of the exact commutant of the supplied almost representation; this is its refutation, in fixed dimension, for every Kazhdan group with a nonabelian finite quotient.
  generic-perturbations-destroy-exact-commutant-gap: that shows an almost-commuting unitary can sit at distance one from the literal commutant; this shows the same failure for a projection that is in addition almost central in the whole approximate commutant, which is the hypothesis of the rounding crux.
  ozawa-sos-does-not-round-approximate-actor-to-exact-commutant: that refutes rounding bounded almost-commuting vectors into the literal commutant of an approximate actor tuple; this refutes rounding almost-central projections to central projections, a regime where property (T) does control the approximate commutant.
artifacts:
  - research/artifacts/hs-median-assembly-audit-2026-09-12.md
---

**ESTABLISHED.** Let `Gamma` be a group, `q : Gamma -> Q` a homomorphism onto a
finite group, and `pi_1 : Q -> U(d)` a nontrivial irreducible unitary
representation with `d >= 2`. Let `F` be a finite generating set of `Gamma`
with `q(F) = Q` and `|F| >= 2`. Put `D = 2d` and use the normalized trace on
`M_D`.

For every `eta > 0` there are a map `theta : Gamma -> U(D)` and a projection
`p in M_D` with `tau(p) = 1/2` such that:

```text
(R1) max_(s,s' in F) ||theta(ss') - theta(s)theta(s')||_op <= C_F eta,
(R2) max_(s in F) ||[p, theta(s)]||_2 <= 2 eta,
(R3) ||[p, x]||_2 <= (1/sqrt(2)) (max_(s in F) ||[x, theta(s)]||_2 + 2 eta)
     for every contraction x in M_D,
(R4) theta(Gamma)' cap M_D = C I,   dist_2(p, {0, I}) = 1/sqrt(2).
```

Here `C_F` depends only on `F` and on one fixed choice of words.

**Consequence for the rounding crux.** Given `delta > 0`, take
`eta = (sqrt(2) - 1) delta / 2`. Then `p` lies in the `delta`-approximate
commutant `A(delta)`, and by (R3) it is `delta`-central in `A(delta)` in the
strongest reading: `||[p, x]||_2 <= delta` for every contraction
`x in A(delta)`. The multiplicative defect is `O(delta)`. Yet the only central
projections of the exact commutant of the supplied matrices are `0` and `I`,
both at 2-distance `1/sqrt(2)`. So no function `f(eps, delta, kappa) -> 0` can
round `p` as `hs-normalization-profile-rounding-crux` asks. This holds in fixed
dimension, so uniformity in `n` is not the issue. The profile clause cannot
help either, since there is no proper nonzero central projection to compare
profiles with.

**Instances with property (T).**
- `SL_3(Z) -> SL_3(F_2)`, which has irreducible representations of dimension at
  least 2.
- The Kun--Thom vertex `EL_3(F_q[x_1,...,x_d]) -> SL_3(F_q)`, by evaluating at
  `x_i = 1`.

In both cases, enlarge a Kazhdan generating set by lifts of all elements of
`Q`. A Kazhdan pair stays a Kazhdan pair when the generating set grows.

**What it does not refute.** The mechanism is that the literal commutant is
discontinuous under operator-norm perturbation. Rounding targets that are
stable under such perturbation are untouched:
- the commutant of a nearby genuine representation after negligible padding;
- the robust low spectral band of the approximate conjugation Laplacian.

The corrected assembly is `hs-normalization-needs-coarse-actor-scale-pinning`.

Derivation: `hs-literal-commutant-profile-rounding-proof`.
