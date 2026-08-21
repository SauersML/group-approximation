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

- **Unified-frontier shot via 1-bounded entropy, and why it does not
  close (2026-08-21).**  All three open program routes -- this Hecke
  face, the `x4`-dynamical KSR face
  (`weyl-defect-koopman-spectral-regularity`), and the factorial-trace
  face (`hnn-carrier-factorial-character-collapse`) -- reduce to ONE
  statement: exclude a non-amenable MIXING `G = PSL_n(Q_p)`-subrep with
  `Lambda`-fixed cyclic vector inside `pi(Lambda)' cap M`.  Fired the
  sharpest tool at it: the enemy factor `N = W*(L(Lambda), k)` is
  strongly `1`-bounded (`Lambda` has (T), so `h(L(Lambda)) = 0`; `k`
  wq-normalizes it, Hayes monotonicity gives `h(N) <= 0`), and
  `N subseteq M` is Connes-embeddable.  So the enemy is a strongly
  `1`-bounded, CE, non-amenable factor carrying a mixing (T)-rep.
  NO CONTRADICTION is available: `L(SL_3(Z))` itself is strongly
  `1`-bounded, non-amenable, and CE, so these properties are mutually
  consistent, and `1`-bounded entropy does not force `k` into
  `pi(Gamma)' cap M`.  This is exactly Alekseev--Thom Open Problem 6.2.
  Closing it needs machinery beyond `1`-bounded entropy / character
  rigidity on the non-amenable part -- the genuine CEP-adjacent
  frontier at which all program routes meet.

- **Refinement: the canonical enemy is the coset wreath group `W`;
  the clean frontier is CE of a non-amenable-stabilizer Bernoulli
  action (2026-08-21).**  The factorial-trace face is NOT a clean
  equivalent of the other two: charmenability of the carrier is FALSE
  (the coset-Bernoulli character is an explicit counterexample, per
  `hnn-carrier-factorial-character-collapse`), so no BBHP dichotomy
  closes it.  What that counterexample exposes is the genuinely
  canonical object: the coset wreath group
  `W = (direct_sum_(Gamma/Lambda) C_2) rtimes Gamma` recurs as THE
  enemy on every face -- it produces the exact quasi-regular leak
  (`coset-bernoulli-ce-refutes-relative-commutant-collapse`), it is
  the charmenability counterexample, and its regular character is the
  vanishing-branch enemy.  So the three faces unify not as an abstract
  spherical-exclusion but concretely: each asks whether `W` is
  hyperlinear, equivalently whether the generalized Bernoulli action
  `L^infinity(K^(Gamma/Lambda)) rtimes Gamma` is Connes-embeddable
  with the NON-AMENABLE stabilizer `Lambda`.  That is the Kun--Thom
  wall in its sharpest arithmetic instance, and it is the single
  concrete frontier object the whole program reduces to -- more useful
  than the abstract `1`-bounded-entropy formulation because `W` is an
  explicit group whose soficity/CE can be attacked directly (the
  `nonhyperlinear-coset-wreath-from-p3-collapse` lane).

- **The goal needs strictly less than this claim.**
  `no-exact-quasi-regular-leak` isolates the single extreme profile
  `s = 0`, `psi = 1_Lambda` — the only configuration a hyperlinear
  `G_2` actually produces — and
  `non-hyperlinear-from-exact-quasi-regular-leak` reaches the goal
  from that alone.  This claim remains the full-collapse form
  (equivalent to `(RCC)`); attack the exact form first.
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
- **Hecke operators contract the leak for `n >= 3` — now a theorem.**
  The contraction sketched here is established as
  `hecke-averaging-realizes-commutant-expectation`: the lazy average
  `S` over one symmetric double coset satisfies `|| S^N(k) - E(k) ||_2
  <= (1 - delta_0)^N || k - E(k) ||_2` with `delta_0 = delta_0(n,p) >
  0` uniform over ALL finite tracial algebras, via a Kazhdan pair of
  the completion bounding the spherical numerical range.  So for the
  higher-rank pair the Gamma-commutant part of any witness is an
  explicit geometric limit of Hecke averages, and this claim itself is
  equivalent (by strict convexity plus expanding generation) to the
  single norm equality
  `single-hecke-average-isometry-for-lambda-central-unitaries`, whose
  finitary translation is the finite-level attack surface.  What the
  contraction alone cannot do is force `s = 1`; the finite-dimensional
  origin of `M` must enter.
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
