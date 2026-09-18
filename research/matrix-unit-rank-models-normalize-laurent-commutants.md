---
rg: 2
id: matrix-unit-rank-models-normalize-laurent-commutants
kind: claim
title: Characteristic-two models whose Laurent elementary vertex satisfies the two-root identity normalize the polynomial commutant, so rank defects for Laurent pairs need N_23 N_12 != 0
distinct_from:
  matrix-unit-rank-models-extract-ring-rank-models: that extracts a ring homomorphism from a matrix-unit model of one EL_3; this uses the extracted corner homomorphism to prove commutant equality C(sigma EL_3(R_+)) = C(sigma EL_3(R)) for a localization R of R_+, and hence normalization for every group normalizing the Laurent vertex.
  bowen-chapman-ambient-rank-models-do-not-round-peripheral: that shows almost-centralizers of honest module models are far from exact commutants, which kills one proof of normalization; this shows those same models, and every model satisfying the two-root identity on the Laurent vertex, do satisfy normalization in the ultraproduct, with no rounding and no property (T).
  laurent-extension-agrees-iff-inverse-defects-commute: that is a Hilbert--Schmidt rounding statement where inverses x^(-1) have unbounded degree; this is an exact rank-ultraproduct statement where the inverse is obtained as the inverse of a corner unit, so degree never enters.
  kazhdan-groups-without-fd-reps-violate-two-root-identity: that constructs models violating the identity for groups without finite-dimensional representations; this shows that for Laurent elementary pairs a normalization failure can only live in models violating it.
  f2-linear-sofic-groups-kill-rigid-compression-defects: that is the open F_2 rank row of the defect criterion; this removes the matrix-unit sector from it for Laurent pairs and decides nothing about the other models.
artifacts:
  - research/artifacts/el3-two-root-identities-2026-09-12.md
  - research/artifacts/el3-rank-ring-rigidity-2026-09-12.md
---

**ESTABLISHED.**

**Setting.**
- `R_+` is a unital subring (containing `1`) of a unital ring `R` of characteristic two. `S` is a set of
  elements of `R_+` that are units of `R`, and `R` is generated as a ring by `R_+` and
  `{s^-1 : s in S}`. Example: `R_+ = F_2[x_1..x_d]` inside `R = F_2[x_1^(±1)..x_d^(±1)]`,
  or `F_2[N^3]` inside `F_2[Z^3]`.
- `Gamma = EL_3(R_+) <= Delta = EL_3(R)`, and `G` is any group containing `Delta` as a
  normal subgroup.
- `M` is any ring of characteristic two, for instance a rank ultraproduct over a field of
  characteristic two. `sigma : G -> M^x` is a homomorphism whose restriction to `Delta`
  satisfies the two-root identity `N_23 N_12 = 0`, where `N_ab = sigma(x_ab(1)) - 1`.

**Theorem.**
1. `C_M(sigma(Gamma)) = C_M(sigma(Delta))`.
2. So `sigma(G)` normalizes `C_M(sigma(Gamma))`.
3. **The general form.** Drop the two-root identity, and let `M` be any unital ring.
   Put `n_ij(a) = sigma(x_ij(a)) - 1`, `N_ij = n_ij(1)`, and, with indices mod 3,

   ```text
   E(a) = sum_i n_(i,i+1)(a) N_(i+1,i).
   ```

   Suppose `(H1)` `E : R -> M` is additive and multiplicative, and `(H2)`
   `n_ij(a) = E(a) N_ij` for all `a` in `R` and `i != j`. Then parts 1 and 2 hold.
   - The matrix-unit case satisfies `(H1)` and `(H2)`.
   - So does every direct sum of a natural-type model, a dual-type model
     `g -> rho(g^(-T))` (for commutative `R`) and a block where `Delta` acts trivially.
     Such a sum violates both `N_23 N_12 = 0` and the dual identity `N_32 N_21 = 0`.

**Consequences.**
- **The Kun--Thom Theorem E pair and the Bowen--Chapman pair.** Take `r = 3`, `q = 2`:
  - `Gamma = EL_3(F_2[x_1..x_d]) <= EL_3(F_2[x^(±1)]) semidirect SL_d(Z)`;
  - `Gamma = EL_3(F_2[N^3]) <= EL_3(F_2[Z^3]) semidirect EL_3(Z)`.

  In every characteristic-two rank ultraproduct model of the ambient group in which the
  Laurent vertex satisfies `N_23 N_12 = 0`, `NORM` holds for the pair. Equivalently, via
  [[rigid-compression-defect-normalization-dichotomy]], the failure-produces-a-witness
  construction produces no rigid defect from such a model.
- **What a counterexample must look like.** A sequence of `F_2`-linear sofic
  approximations `sigma_n` of either ambient group that breaks `NORM` for the pair must have
  `rk(N_23 N_12) >= c n` along the ultrafilter, for some `c > 0`. The identity is exact in
  the ultraproduct, so an `o(n)` violation is covered. Honest module models, degree
  truncations and the Fourier boxes of
  [[bowen-chapman-ambient-rank-models-do-not-round-peripheral]] all satisfy the identity,
  so they cannot host a counterexample however badly their almost-centralizers round.
  Survivors need unit root elements acting with composition factors other than the
  natural module, for example regular modules of finite quotients (Claim C of the
  two-root artifact).
- **For a proof of `NORM_F`.** For these pairs it is enough to handle models with
  `rk(N_23 N_12) > 0` on the Laurent vertex.
- **No property (T), no rounding, no size.** The theorem is exact algebra in `M`. It
  explains why normalization is invisible on module models: there the inverse `x^(-1)`
  is the inverse of a unit of the corner algebra generated by `sigma(Gamma)`, never a
  polynomial of large degree.

**Scope.**
- **Characteristic.** The proof of Part 3 uses no characteristic assumption, but `(H1)`
  forces `e = E(1)` to satisfy `char(R) e = 0`. So for `F_2` coefficients it is non-vacuous
  only in characteristic-two targets. For `R_+ = Z[x_1..x_d]` inside `Z[x^(±1)]` it applies
  in every characteristic, including the complex row
  [[c-linear-sofic-groups-kill-rigid-compression-defects]] for that pair. Only the deduction
  "two-root identity implies `(H1)` and `(H2)`" uses characteristic two. It relies on
  Proposition 6 of `research/artifacts/el3-rank-ring-rigidity-2026-09-12.md`, which uses
  `n_ij(a)^2 = 0`.
- **The honest boundary.** Every model that fails `(H1)` or `(H2)` is untouched. Examples
  are `V (x) V*`, Steinberg-type factors, and regular modules of finite quotients.
- **Rank three.** `EL_r` for `r > 3` needs an `r x r` form of Proposition 6, which is not
  claimed.
- **Not a decomposition.** It is not known whether every model splits into a part that
  satisfies the identity and a remainder, so this does not reduce `NORM` to a smaller
  statement on arbitrary models.

Derivation: [[matrix-unit-rank-models-normalize-laurent-commutants-proof]].
