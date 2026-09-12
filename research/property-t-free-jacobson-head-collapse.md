---
rg: 2
id: property-t-free-jacobson-head-collapse
kind: claim
title: Prove the Jacobson head collapse without property T or Kazhdan transport
distinct_from:
  binary-jacobson-steinberg-head-root-is-mf-invisible: that is the mathematical MF-invisibility statement proved using rank-weighted Kazhdan transport; this requires a proof with no property-T dependency.
---

For J=F_2<S,T | TS=1>, prove that every norm-corona representation of
St_5(J) kills x_13(1-ST), with no use of property (T), Kazhdan
projections, or a theorem whose proof depends on either.

## Attempts

The rank-weighted cutoff argument proves the ordinary head-collapse
statement, but its Section 2 uses one-sided Kazhdan transport. The
elementary uniform support-rank bound and cutoff construction alone
give no replacement for that step. A property-(T)-free proof must
establish the necessary transport or a different obstruction using
additional algebraic structure. This retains that exact missing proof
obligation; it does not reopen the mathematical head statement.

**The root-kernel route is (T)-free in finite dimensions and blocked at
the corona (2026-09-08).**  `uniform-root-kernel-invariance-kills-one-sided-defect`
gives a Kazhdan-free kill of the defect roots: if the two root maps are
genuine additive homomorphisms and the conjugation and commutator tests
hold to within `2 sin(pi/m)` **for every coefficient at one coordinate**,
the common kernel is invariant under left multiplication by `s` and `t`,
`R/I` is finite, and `ts = 1` forces `st = 1` there.  Applied to an exact
finite-dimensional representation of `E_n(R)`, `n >= 3`, the hypotheses
hold with error zero, so no property (T) is needed there at all.

It does not transfer.  `root-kernel-invariance-is-not-pointwise-obtainable`
builds finite models over `J` in which all three root maps are exactly
additive, conjugation transport is exact, the constant Weyl relations are
exact, and every fixed commutator test is eventually **exact** -- and in
which, at every coordinate `N`, the coefficient `s^N` has
`X_N(s^N) = 1` while `Y_N(t s^N)` is at distance `2` from the identity.
So kernel invariance is not obtainable from pointwise corona data, and the
uniform lemma cannot be run against a corona representation.  Reviving this
route means excluding those models with Steinberg relations they do not
realise -- they prescribe nothing at the root positions into a third
coordinate -- which is not done.
