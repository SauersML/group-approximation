---
rg: 2
id: single-hecke-average-isometry-for-lambda-central-unitaries
kind: claim
title: One lazy Hecke average is already isometric on Lambda-central unitaries of every regular-trace matrix model
distinct_from:
  no-spherical-leak-in-matrix-ultraproducts: that excludes a c_0 spherical component of an extended coefficient function; this is a single Hilbert-Schmidt norm equality for one explicit finite word set, whose finitary translation is a checkable matrix inequality -- the finite-level shadow that the leak node's last attempt asks for.
  no-exact-quasi-regular-leak: that refutes the extreme profile s = 0 for the SL_2 pair, where the enemy has an amalgam construction surface at the prime two; this is the n >= 3 (T)-side statement, equivalent to the FULL collapse there, in one-inequality form.
  hecke-averaging-realizes-commutant-expectation: that is an established contraction theorem valid in every finite tracial algebra and silent on the value of the limit; this asserts the limit is trivial -- norm one -- precisely when the algebra is a matrix ultraproduct.
---

Let `n >= 3`, `(Gamma, Lambda) = (SL_n(Z[1/p]), SL_n(Z))`, with
`gamma_0`, the words `w_1, ..., w_L` and the lazy average `S` of
`hecke-averaging-realizes-commutant-expectation`.  Claim: for every
tracial matrix ultraproduct `M`, every trace-preserving regular-trace
representation `pi : Gamma -> U(M)` and every unitary
`k in pi(Lambda)' cap M`,

```text
|| S(k) ||_2 = 1.                                                (SH1)
```

Elementary consequences (recorded here, consumed by the route):
`S(k)` is a convex combination of the `L + 1` unit vectors `k` and
`pi(w_i) k pi(w_i)^*` of `L^2(M)`, so `(SH1)` forces all of them equal
(strict convexity of the Hilbert ball), i.e. `k` commutes with every
`pi(w_i)`, hence with `pi(gamma_0)` (as `w_i = lambda gamma_0
lambda'`), hence with `pi(Gamma)` since `Gamma = < Lambda, gamma_0 >`
(the expanding-conjugation generation recorded in
`sl3-pair-relative-commutant-route` for `n = 3, p = 2` and valid for
all `n >= 3` by the same elementary-matrix scaling).  So `(SH1)` is
equivalent to the full collapse `(RC3)` -- but it is ONE inequality
about ONE explicit operator.

## Attempts

- **Finitary translation.**  By Los and unitary lifting, `(SH1)` is
  equivalent to: for every `c > 0` there are `eta > 0` and a finite
  `F subseteq Gamma` such that no `d`, no map `pi : F -> U(d)` that is
  `eta`-multiplicative and `eta`-regular-trace on `F`, and no unitary
  `k in M_d` with `max_(lambda in F cap Lambda) ||[k, pi(lambda)]||_2
  <= eta` achieve `|| S(k) ||_2 <= 1 - c`.  Every object is finite:
  `L + 1` explicit integer matrices as words, one average, one
  normalized Hilbert-Schmidt norm.  This is the first form of the
  collapse that a computer search can meaningfully attack from the
  refutation side: exhibiting structured `(pi, k)` with definite decay
  at shrinking `eta` would be evidence for a leak, and a proof must
  explain why decay forces multiplicativity failure at a definite
  scale.
- **Probe results (2026-08-21, `experiments/hecke42_average_probe.py`,
  run on sioux).**  Refutation-side Riemannian descent over the
  APPROXIMATE representation variety (six elementary generators,
  `V ~ rho(h)`, witness `k`; Steinberg + `h`-expansion penalties,
  rational-image-certified regular-trace penalty,
  `Lambda`-centrality; polar retraction -- raw numpy QR retraction
  stalls on its R-diagonal phase jumps; analytic word-gradients
  gradchecked to `1e-9`).  With strong penalty weights, EVERY run --
  cold starts at `d = 8` and warm starts on the `Lambda`-exact
  variety (`SL_3(F_2)` permutation model, `d = 14, 28`) -- collapsed
  to `|| S(k) ||_2^2 = 1.0` exactly with `E_C = 0`: descent always
  pushes the witness INTO the full commutant, and the enemy value
  `43/168` was never approached (weak penalties reach it trivially by
  abandoning centrality, which is vacuous).  Consistent with the
  one-commutator modulus and with the prediction of
  `odd-congruence-exact-sector-is-one-inner-action`: an enemy needs a
  deliberately structured `W` acting on the congruence multiplicity
  tower, which naive descent does not build.  A structured follow-up
  should parametrize `W` in the block commutant of a congruence model
  and descend the mixed-trace regularity residual directly.
- **What the established contraction adds.**  By
  `hecke-averaging-realizes-commutant-expectation`, failure of `(SH1)`
  self-amplifies: `|| S(k) ||_2 <= 1 - c` gives
  `|| E(k) ||_2 <= 1 - c`, so the far commutator defect is at least
  `2(2c - c^2)` outside finitely many double cosets and the iterates
  decay geometrically to `|| E(k) ||_2`.  An enemy is therefore never
  marginal: one definite dent in one average certifies a definite
  spherical leak, and conversely.  Any quantitative finite-level
  argument may thus assume the decay is geometric with the explicit
  rate `delta_0(n, p)`.
- **The Lambda-exact odd-congruence sector is CLOSED (2026-08-21).**
  `odd-congruence-lambda-exact-sector-collapses`: if the
  `Lambda`-restriction of the microstates can be taken as genuine
  (necessarily congruence) representations at odd levels, the full
  collapse holds — property (T) lifting plus the three-term Weyl
  relation force the `h`-slot to its congruence value exactly.  So
  any failure of `(SH1)` must have `Lambda`-microstates at UNIFORM
  distance from every exact representation of `SL_3(Z)`: the enemy
  is confined to the representation-variety outlier sector, the
  same residue as the Iwahori and HS-Dehn far sectors.
- **Exact models sit at exactly one, so the enemy is a uniform
  outlier.**  If the microstates can be chosen as genuine
  finite-dimensional representations, property (T) of `Lambda`
  (uniform conjugation gap) moves each `k_m` near
  `rho_m(Lambda)' = rho_m(Gamma)'` (co-density), so `k in
  pi(Gamma)' cap M` and `|| S(k) ||_2 = 1` -- the same mechanism as
  `exact-projective-codensity-has-a-uniform-trace-square-gap` one
  level down.  An enemy achieving `43/168` therefore lives at a
  definite distance from the representation variety at every finite
  level: the fingerprint quantifies the outlier depth the
  Iwahori/HS-Dehn far sector must produce.  Row 2 of
  `rc3-standard-tools-all-fail-audit`: the statement compares exact
  fixed spaces of nested subgroups; almost-invariance technology sees
  only the isolation of each space.  The averaging operator is the
  first object in the lane that couples the two spaces dynamically,
  which is what a finite-level proof must exploit -- e.g. running the
  `(tau)` conjugation gap inside each congruence level of the
  commutant tower against the level spreading forced by the regular
  trace, the attack recorded at the end of
  `no-exact-quasi-regular-leak`.
- **Proof-side SOS is provably unsound here.**  The enemy
  configuration `k = u_t` exists in the genuine tracial model
  `L(H_3)` with every constraint exact and `|| S(k) ||_2^2 =
  43/168`, so by the mechanism of
  `tracial-npa-cannot-separate-canonical-trace` no dimension-blind
  tracial positivity certificate can prove `(SH1)`: its content is
  matrix-only.  Computer work on this node is sound only on the
  refutation side (the probes) or through a genuinely matricial
  proof system.
- **Falsification gate.**  `(SH1)` fails iff the `n >= 3` collapse
  fails iff a spherical leak exists over the higher-rank pair.  In the
  enemy scenario manufactured from a hyperlinear carrier the profile
  is exactly quasi-regular, `psi_k = 1_Lambda`, and the value of the
  average is computed exactly by the coset combinatorics:
  `<pi(w_i) k pi(w_i)^*, pi(w_j) k pi(w_j)^*> = 1_Lambda(w_j^(-1) w_i)
  = delta_(ij)` and each conjugate is orthogonal to `k`, so
  `|| S(k) ||_2^2 = 1/4 + 1/(4L)`; by
  `expanding-double-coset-degree-is-p-times-flags`, `L = p(p+1)(p^2+p+1)`,
  so at the wired pair `(3, 2)` the average runs over `42` words and
  the enemy value is exactly `43/168`.  Any candidate refuting
  construction should be tested against that number first.
