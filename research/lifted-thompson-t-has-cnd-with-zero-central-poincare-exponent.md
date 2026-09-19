---
rg: 2
id: lifted-thompson-t-has-cnd-with-zero-central-poincare-exponent
kind: claim
title: "The lifted Thompson group T-bar has a cnd function psi with sum_m exp(-s psi(z^m)) finite for every s > 0 (superlogarithmic growth along the centre)"
distinct_from:
  lifted-thompson-t-is-a-t-menable: that asks for a proper cnd function on T-bar; this asks for one cnd function whose growth on the centre <z> alone is superlogarithmic, and it implies that target through central-zero-poincare-exponent-gives-euler-splitting
  lifted-thompson-t-center-has-relative-t: that says every cnd function is bounded on <z>; this is a quantitative strengthening of its negation
  thompson-t-euler-class-splits-over-almost-invariant-space: that is the measure-theoretic statement (MT); this cnd growth statement implies (MT), and is not known to follow from it
artifacts: []
---

**Statement (SL for T̄).** `T̄` is the lift of Thompson's `T` to `R`, and `z(x) = x + 1`. There is a
cnd function `ψ` on `T̄` with `δ_z(ψ) = 0`, that is `Σ_{m ∈ Z} exp(−s ψ(z^m)) < ∞` for every `s > 0`.

**Status.** OPEN.

## Role

- It implies (MT) by `central-zero-poincare-exponent-gives-euler-splitting`. Hence it implies
  `lifted-thompson-t-is-a-t-menable`, by `central-extension-haagerup-from-measurable-euler-splitting`
  and Farley. The route is `lifted-thompson-t-a-t-menable-via-central-poincare-exponent`.
- `lifted-thompson-t-is-a-t-menable` implies the weaker statement "some `ψ` has `ψ(z^m) → ∞`". So the
  target and its known necessary condition differ only in the growth rate along one cyclic subgroup:
  superlogarithmic against unbounded.
- A refutation (every cnd `ψ` has `δ_z(ψ) > 0`) would not refute `lifted-thompson-t-is-a-t-menable`.
  It would show that every cnd `ψ` has `ψ(z^m) ≤ C_ψ log|m|` for infinitely many `m`: if
  `ψ(z^m) ≥ (2/s) log|m|` for all large `m`, the sum at `s` converges. Any `s < δ_z(ψ)` then gives
  a contradiction. It would kill this route.

## Known (spectral form, established here)

Let `ψ = ‖b‖²` for a cocycle `b` of an orthogonal representation `π` (complexify). Let `σ` be the
spectral measure of `b(z)` for the unitary `π(z)`, on `θ ∈ (−π, π]`. Since
`b(z^m) = Σ_{i<m} π(z)^i b(z)`,

    ψ(z^m) = ∫ sin²(mθ/2)/sin²(θ/2) dσ(θ) ≤ ∫ min(m², π²/θ²) dσ(θ).

- **No atom at 1.** `σ({0}) = ‖b_1(z)‖²`, where `b_1` is the component in `ker(π(z) − 1)`. Since `z` is
  central, `b_1(z)` is `π(G)`-invariant, so projecting to it gives a homomorphism `T̄ → R` that is
  nonzero on `z` unless `b_1(z) = 0`. `T̄` is perfect (Part 3 of
  `perfect-extension-splittings-are-not-uniformly-integrable`), so `σ({0}) = 0`.
- **Dyadic masses.** Let `A_0 = {1/2 < |θ| ≤ π}`, `A_k = {2^{−k−1} < |θ| ≤ 2^{−k}}` for `k ≥ 1`, and
  `c_k = 4^k σ(A_k)`. On `A_k`, `π²/θ² < 4π²·4^k`. For `2^{K−1} < |m| ≤ 2^K`,

      ψ(z^m) ≤ 4π² Σ_{k ≤ K} c_k + Σ_{k > K} 4^{K−k} c_k.

  So if `sup_k c_k = A < ∞`, then `ψ(z^m) ≤ C A log|m|` and `δ_z(ψ) ≥ 1/(CA) > 0`.
- **Forced shape of any witness.** A witness `ψ` for (SL) has unbounded dyadic masses `c_k`: the
  spectral measure of `b(z)` must put mass `≫ 4^{−k}` on infinitely many annuli `|θ| ≈ 2^{−k}`.
  Mere properness on `⟨z⟩` needs only `Σ_k c_k = ∞`. The borderline case `c_k ≍ 1` gives
  logarithmic growth.

## Attempts

- **Dead: boosting an arbitrary proper `ψ` (2026-09-18, swarm-0917-w13-w13-nv-last1).**
  - Bernstein functions of `ψ` (`ψ^a`, `log(1 + ψ)`) only slow growth down.
  - Spectral reweighting `b ↦ w(π(z)) b` is a cocycle, since `w(π(z))` commutes with `π(G)`. It is
    defined only if `Σ_k |w_k|² ‖E_{A_k} b(s)‖² < ∞` for the generators `s`. The identity
    `(π(z) − 1) b(s) = (π(s) − 1) b(z)` ties the `A_k`-mass of `b(s)` to that of `b(z)` only from
    above. So a weight that makes the `c_k` unbounded is admissible only if the generators' band
    masses decay faster than `b(z)`'s, and nothing forces that.
  - The dilation endomorphism `E(g)(x) = g(2x)/2` of `T̄` (with `E(z) = r_1`, which is not a power of
    `z`) does not move growth between scales of `z`.
