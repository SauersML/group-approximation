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

- **The leak IS the non-Cartan model: my far-sector work is the
  complementary half of Kun--Thom Corollary D (2026-08-21).**
  `coordinate-action-not-sofic` (Kun--Thom Cor D) proves the coset
  action admits no PERMUTATION (Cartan) approximation, so any
  hyperlinear model of `W` must embed the Bernoulli lamp algebra
  NON-Cartanly -- and that non-Cartan model is exactly a leak `k`
  (the `Lambda`-central lamp unitary at the base coset).  So the
  exclusion splits into two complementary halves: Cor D kills the
  Cartan/permutation models (DONE, proven), and excluding the
  NON-Cartan/unitary models is precisely `(NSL1)` / the exact-leak
  question -- the half the whole far-sector architecture attacks.
  The value of that architecture in this light: it supplies a
  genuinely new tool for the non-Cartan half that Cor D cannot reach
  -- the `x4` transfer operator / Livsic / Ruelle--Perron--Frobenius
  reduction (`weyl-defect-koopman-spectral-regularity`), which turns
  "no non-Cartan lamp model" into a dynamical-rigidity statement for
  an expanding circle map.  So the program's two proven-and-open
  halves are: Cor D (Cartan side, closed) + far-sector dynamical
  rigidity (non-Cartan side, the frontier `(KSR)`), and `W`
  non-hyperlinear is exactly their conjunction.  This is the cleanest
  statement of what remains: one dynamical-rigidity theorem for `x4`,
  complementing an already-proven combinatorial one.

- **Popa--Vaes W*-rigidity checked, does not reach (2026-08-21).**
  For `Gamma` with property (T) the Bernoulli crossed product `L(W)`
  has the lamp algebra as its UNIQUE Cartan (Popa / Ozawa--Popa
  strong rigidity).  A hyperlinear `W` embeds `L(W)`, hence that
  unique Cartan `A`, into the matrix ultraproduct `M`, where Cor D
  forbids permutation-approximating `A`.  This would close the goal
  IF a masa normalized by an approximate representation inside a
  matrix ultraproduct were forced to be permutation-approximable
  (Cartan-like).  No such ultraproduct-masa-normalization rigidity
  exists -- masas in `R^omega`-type ultraproducts can be exotic and
  need not be AFD-normalized -- so the internal uniqueness of the
  Cartan does not transfer to an obstruction inside `M`.  Toolkit
  survey now complete: `1`-bounded entropy (consistent, no
  contradiction), character rigidity / charmenability (amenable part
  only; charmenability of the carrier is false), Popa--Vaes Cartan
  rigidity (internal, does not transfer), and elementary
  near-identity forcing (fails at the Weyl swap) all checked and
  mapped.  The non-Cartan exclusion is beyond the standard operator-
  algebraic toolkit; the far-sector `x4` dynamical-rigidity route
  (`weyl-defect-koopman-spectral-regularity`) is the one genuinely
  new instrument aimed at it, and it is the live frontier.

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
- **The enemy has NO forced decay profile (corrected 2026-08-21 audit).**
  An earlier bullet asserted that in the quasi-regular scenario the leak
  follows the Harish-Chandra `Xi` decay.  False on both counts: the
  coefficient of the `K`-fixed vector of `L^2(G/K)` is the indicator
  `1_K` (`K` open, `G/K` discrete), and the canonical enemy indeed has
  `psi_k = 1_Lambda` exactly -- far FASTER than `Xi`; and for `0 < s < 1`
  the `c_0` spherical component need not be tempered, since
  `PSL_n(Q_p)` (`n >= 3`) has spherical complementary series that
  property (T) does not exclude.  Any quantitative attack that extracts a
  contradiction from `Xi`-rate decay is therefore aimed at the wrong
  object; the honest far-sector datum is only `c_0`-ness.
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
