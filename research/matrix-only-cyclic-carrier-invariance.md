---
rg: 2
id: matrix-only-cyclic-carrier-invariance
kind: claim
title: Force a transverse cyclic carrier to become invariant only in finite matrices
distinct_from:
  fanizza-canonical-profile-groupification: that asks to collapse the native machine signal along canonical microstates; this asks only for a finite-dimensional invariance estimate on a cyclic Fourier carrier with independently certified canonical transversality.
  robust-locally-satisfiable-relator-code: that seeks a direct positive fraction of violated word relators; this permits the contradiction to be mediated by one property-T commutator-energy inequality.
  property-t-hs-positive-density-commutant-no-growth: that supplies a lower/no-growth theorem in approximate HNN models; this asks for the opposite matrix-only upper bound which is allowed to fail in the canonical regular von Neumann algebra.
---

Construct a finitely presented group `G=<X|R>`, a property-`(T)` subgroup
`H=<S>`, an infinite-order word `w`, and a nonconstant trigonometric
polynomial `f` such that every nonzero power of `w` in the Fourier support of
`f` has infinite `H`-conjugacy orbit, while the following genuinely
finite-dimensional estimate holds.

There is a modulus `eta(delta)->0` such that every finite-dimensional unitary
tuple `U` with presentation defect at most `delta` satisfies

```text
sum_(s in S)||[U(s),f(U(w))]||_2^2 <=eta(delta).         (MCI1)
```

The estimate must use finite-dimensional multiplicity, rank, or recursion.
It cannot be a formal consequence of the group relations or a dimension-free
Hilbert-space inequality, since the regular representation satisfies those
relations and has the strict lower floor from
`infinite-conjugacy-orbits-give-canonical-carrier-no-capture`.

## Attempts

- `mci-exact-endpoint-is-fd-radical` identifies the zero-defect requirement,
  but `shifted-infinite-heisenberg-wreath-exact-mci-is-hyperlinear` realizes
  that entire endpoint with an infinite-order transverse carrier inside a
  hyperlinear group. The missing statement is uniformity as dimension grows,
  not exact finite-dimensional representation theory.
- Amenable shift-local recursion cannot prove `(MCI1)` by
  `amenable-finite-propagation-feedback-has-folner-tail-models`.
- Property `(T)` supplies the lower floor, not the upper bound;
  `property-t-does-not-force-marked-carrier-transversality` shows that it
  cannot manufacture orbit transversality.
- A finite-at-each-stage word recursion cannot amplify a sublinear exceptional
  summand by `word-recursion-cannot-amplify-sublinear-summands`. A viable
  construction must act on the canonical macroscopic carrier and use a
  matrix-only capacity or holonomy recurrence.
- `cyclic-carrier-energy-stability` is a strict weakening: it permits nonzero
  exact finite-dimensional energy and asks only that one scalar energy
  supremum be upper semicontinuous at zero defect.
