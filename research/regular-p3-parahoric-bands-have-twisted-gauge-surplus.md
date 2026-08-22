---
rg: 2
id: regular-p3-parahoric-bands-have-twisted-gauge-surplus
kind: claim
title: Regular p-three parahoric bands contain a full inverse twisted gauge with dimension surplus
distinct_from:
  finite-native-p3-atlas-has-a-global-inverse-groupoid-gauge: that constructs some finite inverse gauge for an arbitrary fixed chart groupoid; this computes the gauge already present, with multiplicity, inside each canonical regular finite-parahoric block.
  projective-holonomy-rank-forces-exponential-multiplicity: that lower-bounds multiplicity when a binary projective form of rank two-r is imposed; this shows canonical regular blocks automatically supply the entire inverse twisted regular module, whatever that lower bound is.
  regular-congruence-depth-mixtures-remain-folner: that computes the genuine conductor-depth weights and canonical character of regular congruence mixtures; this computes the internal Clifford multiplicity on every one of those regular bands.
---

Let `P` be a finite parahoric quotient, `N normal P` its finite Heisenberg
radical, and `pi in Irr(N)` an invariant oscillator type of dimension `d`.
Put `L=P/N`, and let `alpha` be the Mackey multiplier of chosen oscillator
intertwiners.  Then the `pi`-isotypic part of the left regular representation
of `P` is

```text
Reg(P)[pi] = H_pi tensor (d Reg_(alpha^(-1))(L)).        (RGS1)
```

Here `Reg_(alpha^(-1))(L)` is the inverse twisted left-regular module.  In
particular the external multiplicity dimension is

```text
m_pi = d |L|,                                           (RGS2)
```

and it contains `d` complete copies of the gauge that cancels every
little-group cocycle relation.

Indeed, restriction of `Reg(P)` to `N` is `|L| Reg(N)`, so its
`pi`-isotypic dimension is `|L|d^2`.  Clifford factorization identifies the
multiplicity action as an `alpha^(-1)`-projective `L`-module.  The regular
character on the crossed-product corner, or equivalently the projective
irreducible decomposition

```text
Reg_(alpha^(-1))(L)
 = direct_sum_(sigma) (dim sigma) sigma,                (RGS3)
```

then gives `(RGS1)`.  If `pi` has a nontrivial `P`-orbit, apply the same
calculation in its inertia subgroup and induce; the conclusion on each orbit
packet is unchanged.

For a regular congruence block `Reg(G_a)`, restriction to its parahoric is
`[G_a:P_a] Reg(P_a)`, so `(RGS1)` occurs with still larger multiplicity.
For an arbitrary direct sum of regular blocks at different conductor depths,
the inverse gauges occur blockwise.  No gauge must be shared between
orthogonal conductor central summands: their required dimensions and their
available ambient dimensions both add.

Consequently an unbounded twisted-regular size as `a->infinity`, even if it
occurs, gives no same-model capacity contradiction.  The canonical regular
block at depth `a` has already budgeted at least that entire module.  The
positive odd-depth mass supplied by
`one-shift-folner-mass-is-depth-parity-balanced` only lower-bounds the direct
sum of such cancellable blocks; it does not tensor their cocycle ranks or
place them on one common multiplicity reservoir.

This is an exact recycling escape from the capacity version of the p-three
flux route.  To obtain a supercritical inequality one must authenticate that
many depth packets act **simultaneously on the same multiplicity factor**, so
their projective ranks add while the available dimension does not.  Depth
weights, parity balance, regular character, and separate finite-parahoric
tables provide only orthogonal direct-sum incidence and cannot imply that
common-reservoir condition.
