---
rg: 2
id: kazhdan-almost-invariant-corner-near-invariant-projection
kind: claim
title: Under a genuine Kazhdan representation, an almost-invariant finite-rank projection is near an exactly invariant one of the same normalized rank
distinct_from:
  kazhdan-weak-ucp-stability-is-flexible-stability: that applies this lemma to the Stinespring corner of a weakly ucp-stable group and draws the stability conclusion; this is the bare operator lemma, for a genuine representation on any Hilbert space, with explicit constants, so that other lanes can force exact block structure from approximate invariance.
  one-commutator-controls-distance-to-full-commutant: that is a Kazhdan-type comparison for Lambda-central vectors against the full commutant expectation in the arithmetic Hecke lane; this is the general finite-rank-projection form of the Kazhdan lemma with operator-norm control obtained by averaging, independent of any Hecke structure.
  gowers-hatami-finite-group-hs-stability: that corrects an almost-HOMOMORPHISM of a finite group to a genuine representation; this assumes a genuine representation already and corrects an almost-invariant SUBSPACE to an invariant one, the complementary tool.
---

**LEMMA.**  Let `Gamma` be a group with Kazhdan pair `(S, kappa)`,
`S = S^(-1)` finite, and `pi : Gamma -> U(H)` a genuine unitary
representation on a Hilbert space `H` of any dimension.  Let `P` be a
projection of finite rank `d` with

```text
max_(s in S) || [pi(s), P] ||_HS  <=  eta sqrt d,      eta < 1/22,   (KA1)
```

`|| . ||_HS` the unnormalized Hilbert--Schmidt norm.  Then there is a
projection `E` of finite rank `d'` commuting with `pi(Gamma)` such that

```text
|| E - P ||_HS <= (11 / kappa) eta sqrt d,
| d' - d |     <= (121 / kappa^2) eta^2 d,                          (KA2)
```

and a partial isometry `W : ran P -> ran E` with
`|| W - P ||_HS <= (22 / kappa) eta sqrt d`.  In particular `ran E` is a
`pi(Gamma)`-invariant subspace of normalized rank `d'/d = 1 + O(eta^2)`
and `pi|_(ran E)` is a genuine finite-dimensional representation whose
compression differs from `P pi(.) P` by `O(eta)` in normalized HS norm.

**What it is for.**  Any construction that produces an almost-invariant
finite corner inside a genuine Kazhdan representation -- dilations of ucp
maps, exact finite-group cores inside a larger (T) group, property-`(tau)`
families of finite quotients with a uniform Kazhdan constant -- can
replace the corner by an exactly invariant one at linear cost in the
defect and quadratic cost in dimension.  The operator-norm control of the
intermediate averaged operator is the one non-obvious point: the nearest
invariant vector in `HS(H)` has no operator-norm bound, but the limit of
lazy Kazhdan averages of `P` is a positive contraction, and only then does
the spectral cut-off at `1/2` give a projection of the right rank.

**Ultraproduct corollary.**  Let `rho_n` be genuine finite-dimensional
unitary representations of a Kazhdan `Gamma` and
`M = prod_U M_(d_n)` the tracial ultraproduct, `pi = [rho_n]`.  Then

```text
pi(Gamma)' cap M = prod_U ( rho_n(Gamma)' cap M_(d_n) ) :          (KA3)
```

any `u in pi(Gamma)' cap M` lifts to a bounded sequence `(u_n)` with
`|| [u_n, rho_n(s)] ||_(2,d_n) -> 0` for the finite Kazhdan set, and the
lazy averages `P_inv(u_n) in rho_n(Gamma)'` (contractions, as in the
proof) satisfy `|| P_inv(u_n) - u_n ||_(2,d_n) -> 0`; the reverse
inclusion is levelwise.  So on the exact sector the relative commutant is
itself an ultraproduct of finite-dimensional commutants — the
normalized-HS analogue of Alekseev--Thom's theorem that the centralizer
of a sofic embedding of a Kazhdan group is a metric ultraproduct of
permutation centralizers (arXiv:2608.05362), and the standalone form of
the "(T)-lifting into the congruence commutant tower" steps of
`odd-congruence-lambda-exact-sector-collapses`.  For INEXACT microstates
nothing of the sort holds — that gap is the correctability frontier
(`sl3z-regular-microstates-are-congruence-correctable`).

**What it is not.**  It does not correct an almost-REPRESENTATION: if
`pi` is only approximately multiplicative, `Ad pi` is not a
representation and property (T) has nothing to act on.  For finite
groups that gap is closed by `gowers-hatami-finite-group-hs-stability`
first; for infinite Kazhdan groups it is exactly the stability question
(`sln-z-flexibly-hs-stable`, `sl3-z-weakly-ucp-stable`).
