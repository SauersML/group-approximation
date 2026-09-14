---
rg: 2
id: free-group-injective-ca-preserve-bernoulli-via-f-invariant
kind: claim
title: Over a free group the f-invariant forces every injective automaton to preserve the uniform Bernoulli measure
distinct_from:
  every-injective-ca-preserves-uniform-bernoulli-measure: that is the universal statement over every group, equivalent to Gottschalk; this is the free-group case, proved by a measure-conjugacy invariant with no finite models.
  bijective-ca-preserve-uniform-bernoulli-measure: that assumes bijectivity over any group; this assumes only injectivity, over free groups, and deduces preservation from an entropy invariant.
  residually-finite-groups-are-surjunctive: that proves surjunctivity of free groups through finite quotients; this proves the stronger measure statement without any finite model, as a calibration of mass-transport methods.
artifacts:
  - research/artifacts/free-group-f-invariant-bernoulli-preservation-2026-09-12.md
---

Let `G = F_r`, `A` a finite alphabet with `q = |A|`, and `tau` an injective cellular
automaton on `A^G`. Then `tau_* mu = mu`, where `mu` is the uniform product measure.
So `tau` is surjective, by `injective-measure-preserving-ca-is-surjective`.

The proof uses no finite quotient and no sofic approximation. `tau` is a measure
conjugacy onto its image, so Bowen's f-invariant gives `f(tau_* mu) = f(mu) = log q`.
Bowen's functional `F(alpha) = (1-2r)H(alpha) + sum_i H(alpha v s_i alpha)` is
non-increasing under splitting, which is elementary submodularity. On ball windows it
is bounded above by `H(B_n) - sum_i H(B_n ∩ s_i B_n)`. The tree identity
`|B_n| - sum_i |B_n ∩ s_i B_n| = 1` then forces, by induction on `n`, a uniform law on
every ball.

**Calibration.** This is the mass-transport balance of the Cayley tree in entropy
form. The artifact's Section 5 records the three places where the same argument cannot
be run:
* two-cells, where the three-set inclusion–exclusion bound fails on duplicated
  coordinates;
* Kazhdan hosts, which have FA;
* non-unimodular trees.

**ESTABLISHED 2026-09-12** by
[[free-group-bernoulli-preservation-via-f-invariant-proof]].
