---
rg: 2
id: no-exact-quasi-regular-leak
kind: claim
title: No matrix ultraproduct carries an exactly quasi-regular leak over the arithmetic pair
distinct_from:
  no-spherical-leak-in-matrix-ultraproducts: that excludes every leak (all values of the commutant mass s, equivalent to the full collapse); this excludes only the single extreme profile s = 0 with EXACT quasi-regular coefficients, which is all the goal consumes.
  relative-commutant-collapse-for-sl2-pair: that is the full relative-commutant identity quantified over every element; this is one forbidden configuration, strictly weaker to refute, and it reaches the goal directly without the collapse as middleman.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that shows Connes embeddability of the coset Bernoulli action would PRODUCE this configuration; this asserts the configuration cannot occur in regular-trace matrix models, and is therefore exactly the negation gate of that construction.
---

Let `M = prod_U M_(d_m)` be a tracial matrix ultraproduct,
`Gamma = SL_2(Z[1/2])`, `Lambda = SL_2(Z)` (the family
`SL_n(Z[1/p])` over `SL_n(Z)` is identical).  There is no
trace-preserving representation `pi : Gamma -> U(M)` with regular
restricted trace together with a unitary `k in pi(Lambda)' cap M`
satisfying the EXACT quasi-regular profile

```text
tau(k* pi(gamma) k pi(gamma)*) = 1_(Lambda)(gamma)
for all gamma in Gamma.                                  (EQL1)
```

Equivalently, by `hecke-far-commutator-defect-formula`: no exact
`Gamma`-equivariant isometric copy of `l^2(Gamma/Lambda)` inside the
`Ad pi` representation on `L^2(M)` has its base vector realized by a
`Lambda`-central UNITARY of `M`.

By `non-hyperlinear-from-exact-quasi-regular-leak` this claim alone
produces the explicit finitely presented non-hyperlinear group `G_2`
of `(SZ1)`; no relative-commutant collapse and no stability hypothesis
intervenes.

## Attempts

- **This is the extreme point, not the generic leak.**  The far-defect
  formula splits every leak as `psi_k = s + (1-s) phi` with `phi` a
  `c_0` spherical coefficient; refuting only `s = 0` with `phi` the
  exact quasi-regular spherical function already suffices for the
  goal, because the enemy manufactured from a hyperlinear `G_2` has
  profile exactly `1_Lambda`.  All prior routes demanded the full
  collapse (`every` `k`); this hole quantifies over one configuration.
- **The enemy is a uniform representation outlier — unconditionally.**
  Suppose `(EQL1)` holds along microstates `U_m` whose `Gamma`-part is
  within `eta` (on generators, normalized HS) of an exact
  finite-dimensional representation.  The exact profile at any
  `a_1 notin Lambda` gives `||[k, pi(a_1)]||_2 = sqrt(2)`, while the
  quantitative estimate `(HC2)` of
  `hnn-over-codense-kazhdan-subgroup-not-hyperlinear`, fed by the
  co-density and uniform `(tau)` conjugation gap of
  `sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`, bounds this
  commutator by `C_0((tau_defect + eta)/kappa + |a_1| eta)`.  So there
  is an explicit `c > 0` with `eta >= c` for all `m` along the
  ultrafilter: the enemy microstates can NEVER approach the exact
  representation variety.  The residual regime is precisely the
  uniform-outlier sector — the same residue as the Iwahori
  `iwahori-outlier-repair` and the HS-Dehn far sector, now with the
  extra exactness `(EQL1)` to exploit against it.
- **The enemy's coefficients are tempered.**  The GNS representation
  of the extended profile is the spherical part of
  `L^2(PSL_2(Q_2)/K)`, so all far coefficients ride the
  Harish--Chandra `Xi` decay; any refutation only has to beat
  quasi-regular decay, not arbitrary `c_0` decay (contrast the
  complementary-series-shaped leaks the full collapse must also
  exclude).
- **Known would-be producers.**  Connes embeddability of the coset
  Bernoulli crossed product `L^infinity(K^(Gamma/Lambda)) rtimes Gamma`
  would produce `(EQL1)` with `k = 2P - 1` for the coordinate
  projection `P` at the base coset (trace `1/2`, conjugates exactly
  uncorrelated) — recorded as
  `coset-bernoulli-ce-refutes-relative-commutant-collapse`.  Soficity
  or CE of Bernoulli actions with NON-amenable stabilizer is open and
  is the Kun--Thom wall; so a refutation of `(EQL1)` will in
  particular prove that this coset Bernoulli action is not CE with
  the regular marginal trace — the two questions stand or fall
  together at this profile.
- **Where finite-dimensionality must enter.**  In `L(G_2)` itself the
  configuration exists, so no trace identity alone can refute it.
  The regular restricted trace forces the finite-level restrictions
  `U_m|_Lambda` to spread across congruence levels (every
  finite-dimensional `Lambda`-isotype has vanishing normalized
  weight in the limit), while `k` must remain exactly central for
  `pi(Lambda)` and exactly uncorrelated with its `pi(gamma)`
  conjugates.  The recorded attack is to run the `(tau)` conjugation
  gap INSIDE each congruence level of the commutant tower
  `U_m(Lambda cap gamma Lambda gamma^(-1))'` and show level spreading
  is incompatible with exact uncorrelation at every shell — the
  finite-level shadow of the Hecke contraction recorded in
  `no-spherical-leak-in-matrix-ultraproducts`.
