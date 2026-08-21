---
rg: 2
id: no-spherical-leak-in-matrix-ultraproducts
kind: claim
title: Matrix ultraproducts admit no spherical leak over the arithmetic Hecke pair
distinct_from:
  relative-commutant-collapse-for-sl2-pair: logically equivalent to it through the far-defect formula, but restated so the unknown is one scalar per element and the enemy is a c_0 spherical representation; the collapse statement itself exposes neither the Hecke-operator contraction nor the Xi decay profile.
  kt-centralizer-normalization-hs: that normalizes centralizers for the Kun-Thom compressor pair; this excludes mixing spherical components for the arithmetic pair inside the ambient ultraproduct commutant.
---

Let `M = prod_U M_(d_n)` be a tracial matrix ultraproduct,
`pi : Gamma -> U(M)` a trace-preserving regular-trace representation of
`Gamma = SL_n(Z[1/p])`, and `Lambda = SL_n(Z)`.  Then every unitary
`k in pi(Lambda)' cap M` satisfies

```text
|| E_(pi(Gamma)' cap M)(k) ||_2 = 1,                     (NSL1)
```

equivalently (by `hecke-far-commutator-defect-formula`) the extended
coefficient function `psi_k` on `G = PSL_n(Q_p)` has no nonzero `c_0`
spherical component: no Hilbert--Schmidt-central witness for `Lambda`
can carry a mixing `G`-representation in its `Ad`-cyclic subspace.

This is exactly what fails for `M = L(HNN)` itself, so the content is
the finite-dimensionality of the microstates, not tracial abstraction.

## Attempts

- **Falsification gate and equivalence.**  If the co-dense HNN group of
  `non-hyperlinear-from-relative-commutant-collapse` is hyperlinear,
  its stable letter provides `k = u_t` with `[k, pi(Lambda)] = 0` and
  `[k, pi(diag)] != 0`, hence `s < 1`: a spherical leak exists and
  `(NSL1)` is false.  Conversely a leak refutes `(RCC)` directly.  So
  this claim is a reformulation of the collapse, not a weakening — its
  value is the new attack surface, not logical progress by itself.
- **The enemy has a forced decay profile.**  In the quasi-regular
  scenario (`psi_k -> 0` far out, `E(k) = 0`), the leak is the
  `K`-spherical vector of `L^2(G/K)`, which is tempered: the far
  coefficients must follow the Harish--Chandra `Xi` decay in the
  double-coset length.  A finite-level transfer would say: the matrices
  `K_n` realizing `k` have `Ad pi_n(gamma)`-coefficients tracking a
  spherical function of a group that `pi_n` does not see.  Matching
  this against the HS-Dehn far-sector length control
  (`research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md`)
  is the quantitative attack.
- **Hecke operators contract the leak for `n >= 3`.**  For a double
  coset `Lambda gamma Lambda = sqcup gamma_i Lambda`, the average
  `T_gamma(k) = (1/[Lambda gamma Lambda : Lambda]) sum_i pi(gamma_i) k
  pi(gamma_i)*` is again `Lambda`-central (left multiplication by
  `Lambda` permutes the cosets), lies in `M`, and satisfies
  `E(T_gamma(k)) = E(k)`.  Its action on the `c_0` part of the GNS
  space has norm the spherical eigenvalue at `gamma`.  For `n >= 3`,
  `G` has property (T), the trivial representation is isolated, and the
  class-one `c_0` spectrum is uniformly bounded away from `1` at a
  fixed `gamma`: Hecke iteration converges geometrically,
  `T_gamma^N(k) -> E(k)` in `|| ||_2`.  So for the higher-rank pair the
  Gamma-commutant part of any witness is an explicit geometric limit of
  Hecke averages — a concrete handle the bare collapse statement never
  offered.  What iteration alone cannot do is force `s = 1`; the
  finite-dimensional origin of `M` must enter.
- **The amenable sector is already closed.**  Dogon--Vigdorovich
  hyperfinite HS-stability (via character rigidity) settles `(RCC)`
  when the relevant commutant piece is amenable.  Combined with the
  splitting: any surviving leak generates a NON-amenable mixing
  `Gamma`-subrepresentation with `Lambda`-fixed cyclic vector inside
  `pi(Lambda)' cap M`.  So the hole is exactly: exclude a non-amenable
  tempered-type spherical module inside a matrix ultraproduct
  commutant.  This matches the recorded far-sector residue of the
  HS-Dehn lane (non-amenable coupling only) and gives it the missing
  representation-theoretic shape.
