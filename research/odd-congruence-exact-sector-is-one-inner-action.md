---
rg: 2
id: odd-congruence-exact-sector-is-one-inner-action
kind: claim
title: In the odd-congruence exact sector the collapse is the triviality of one inner action on the congruence commutant tower
distinct_from:
  single-hecke-average-isometry-for-lambda-central-unitaries: that is the full collapse in one-inequality form over ALL regular-trace models; this reduces its Lambda-exact odd-congruence sector to a statement about a single unitary acting on an explicit ultraproduct of multi-matrix inclusions, and identifies where the enemy's freedom sits.
  odd-congruence-vertex-sector-admits-no-exact-leak: that CLOSES the odd sector for the exact SL_2 profile via the amalgam's vertex structure and the normal-closure squeeze; this is the SL_3 analysis, where there is no amalgam, the reduction goes through innerness of h mod odd n, and the sector is reduced, not yet closed.
  rc3-standard-tools-all-fail-audit: its row 4 says co-density fails because ultraproduct vectors need not come from genuine representations; this works INSIDE the sector where they do, and shows exactly what survives there -- one inner action -- so the sector is not vacuously closed by co-density.
---

Let `Gamma = SL_3(Z[1/p])`, `Lambda = SL_3(Z)`, `h = diag(p, 1,
p^(-1))`, `Lambda_- = Lambda cap h^(-1) Lambda h` (a parahoric of
index `L = p(p+1)(p^2+p+1)`).  Call a trace-preserving regular-trace
representation `pi : Gamma -> U(M)`, `M = prod_U M_(d_m)`,
**Lambda-exact of odd congruence type** if it admits microstates
whose `Lambda`-restrictions are genuine finite-dimensional unitary
representations `sigma_m` -- necessarily factoring through congruence
quotients `SL_3(Z/n_m)` (Margulis superrigidity for compact targets
plus the congruence subgroup property) -- with all `n_m` odd and
coprime to `p`.  Then:

1. **The exact slot is inert.**  Since `p` is invertible mod `n_m`,
   `h` has an image in `SL_3(Z/n_m)` and `V'_m = sigma_m(h mod n_m)`
   lies in the image of `Lambda` (surjectivity mod `n_m`), so
   `Ad(V'_m)` is TRIVIAL on the commutant `sigma_m(Lambda)'`.
2. **The whole enemy is one unitary.**  Writing `V = pi(h)` and
   `V' = [V'_m]`, the corrector `W := V'^* V` lies in
   `pi(Lambda_-)' cap M` (the conjugation relations for
   `lambda in Lambda_-` hold exactly for both `V` and `V'`), and for
   every `k in pi(Lambda)' cap M`,

   ```text
   [k, V] = V' [k, W].                                          (OI1)
   ```

   Hence the collapse `(RC3)` restricted to this sector is EQUIVALENT
   to: `Ad(W)` acts trivially on `pi(Lambda)' cap M` for every such
   `W` compatible with the regular trace of `Gamma`.
3. **The arena is an explicit Bratteli ultraproduct.**  The inclusion
   `pi(Lambda)' cap M subseteq pi(Lambda_-)' cap M` is the
   ultraproduct of the finite-dimensional inclusions
   `sigma_m(Lambda)' subseteq sigma_m(Lambda_-)'`, i.e. of
   multi-matrix inclusions whose Bratteli data is the branching of
   `Res^Lambda_(Lambda_-)` on the dual of `SL_3(Z/n_m)`; the
   regular-trace hypothesis says the trace weights spread across the
   levels.  The open sector question is thus: can a unitary `W` of
   the big tower act nontrivially on the small tower while every
   mixed `Gamma`-word trace (in particular the whole `h`-power
   solenoid tower `tr((V'W)^j)`) is regular?

## Attempts

- **SUPERSEDED IN THE STRONGEST WAY (same day):**
  `odd-congruence-lambda-exact-sector-collapses` closes the sector
  outright — property (T) lifting puts `W` in the congruence
  commutant tower, where the three-term Weyl-orbit relation
  `h' = h h''^(-1)` evaluates `W = 1` exactly, no trace hypothesis
  needed.  The reduction recorded here remains the scaffolding of
  that proof; the level-spreading attack anticipated below turned
  out to be unnecessary for this sector.
- **Relation to the one-commutator modulus.**  By
  `one-commutator-controls-distance-to-full-commutant`, in this
  sector `|| [k, W] ||_2 = || [k, pi(h)] ||_2 >= 2 sqrt(delta_0)
  dist_2(k, pi(Gamma)' cap M)`: the inner action's displacement on
  each `k` is bounded below by its leak distance -- `W` cannot act
  slightly on many `k`'s; any nontriviality is macroscopic.
- **Probe consistency.**  The numerical floor of
  `experiments/hecke42_average_probe.py` (all runs collapse to
  `||S(k)||_2^2 = 1`, `E_C = 0`) is what this reduction predicts for
  unstructured searches: without a deliberately built `W` acting on
  the multiplicity tower, descent finds only the inert configuration.
  A structured follow-up probe should parametrize `W` directly in the
  block commutant of a congruence model and descend the mixed-trace
  regularity residual.
- **The Weyl relations constrain the corrector — and kill every
  translation-type ansatz (2026-08-21, worked out).**  The relation
  `w h w^(-1) = h^(-1)` holds EXACTLY in `Gamma` for the signed
  permutation `w = w_13 in Lambda` (conjugation inverts the diagonal),
  so in `M`: substituting `V = V' W` and `w h w^(-1) = h^(-1) mod n`,

  ```text
  lambda(w) W lambda(w)^(-1) = V' W^(-1) V'^(-1),          (OI2)
  ```

  and the three-term Weyl-orbit relation `h = h' h''^(-1)` couples the
  correctors of the conjugate diagonals likewise.  Consequence: a
  corrector of pure right-translation type on a regular level (the
  "group-like/abelian" ansatz `W = rho(g)`) must define an
  `S_3`-invariant homomorphism from the coweight lattice of `SL_3`,
  and the `S_3`-COINVARIANTS OF THE COWEIGHT LATTICE VANISH (each
  transposition negates a root coweight and the cycle identifies
  them), so `W = 1`: no translation-type enemy exists at any odd
  level.  For `SL_2` the coinvariants are `Z/2` — exactly the ONE
  INVOLUTION of the Iwahori square-root presentation
  (`iwahori-square-root-presentation-is-bs14-plus-one-involution`),
  i.e. the known `SL_2` enemy seed.  The rank-two Weyl system `(OI2)`
  is the structural asset the higher-rank sector has and `SL_2` does
  not; the open question is whether `(OI2)` plus mixed-trace
  regularity forces `Ad(W)` trivial on `pi(Lambda)' cap M` for
  GENERAL `W`, not just translation type.
- **Falsification gate.**  A `W` witnessing sector failure yields a
  leak, hence refutes `(RC3)` and, through the carrier
  correspondence, produces a hyperlinear character of the carrier
  with nontrivial two-block moments over odd-congruence data -- the
  `SL_3` shape of the configuration whose `SL_2` odd-sector
  analogue is EXCLUDED; comparing the two mechanisms (normal-closure
  squeeze there, branching-tower here) is the sharpest place to look
  for either a proof or a construction.
