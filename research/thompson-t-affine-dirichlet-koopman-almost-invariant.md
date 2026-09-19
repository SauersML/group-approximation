---
rg: 2
id: thompson-t-affine-dirichlet-koopman-almost-invariant
kind: claim
title: "In the Dirichlet-space model of Thompson's T, the Koopman representations of the affine nonsingular Gaussian actions x -> rho(g)x + t c(g), t != 0, jointly have almost invariant vectors"
distinct_from:
  thompson-t-linear-gaussian-koopman-has-spectral-gap: that proves the linear (t = 0) Koopman representation has no almost invariant vectors; this asks the same question for the affine actions t != 0, where the translation part is unbounded on PSL_2(Z) and that proof does not apply
  symplectic-gaussian-actions-split-area-cocycles: that gives the splitting over every X_t and makes almost invariance of the linear representation sufficient; this is the affine almost invariance that the splitting needs once the linear one is dead
  thompson-t-euler-class-splits-over-almost-invariant-space: that is (MT) for an arbitrary nonsingular space; this is (MT) restricted to one explicit family of spaces, the affine Gaussian spaces of the Dirichlet model, and implies it
artifacts: []
---

**Status.** OPEN.

**Setting.** Use the smoothed model of
`thompson-t-dirichlet-space-restricted-symplectic-model`: `H = H^{1/2}(R/Z)/R`,
`ρ(g)φ = φ∘g^{-1}` in `Sp_res`, `c(g) = u_{g^{-1}}`. Use the notation of
`symplectic-gaussian-actions-split-area-cocycles`: `γ` is the standard Gaussian measure on `X`,
`A^t_g = τ_{tc(g)} ∘ ρ(g)^` is the nonsingular affine action on the conull set `X_t`, and
`κ_t(g) = κ(A^t_g) = κ(τ_{tc(g)}) κ₀(g)` is its Koopman representation on `L²(X, γ)`.

**Statement (G_aff).** There are reals `t_n ≠ 0` and unit vectors `ξ_n ∈ L²(X, γ)` with
`‖κ_{t_n}(g)ξ_n − ξ_n‖ → 0` for every `g ∈ T`.

Equivalently, the Koopman representation `⊕_n κ_{t_n}` of the disjoint union `⊔_n X_{t_n}` has
almost invariant vectors for some sequence `t_n ≠ 0`. The special case of a constant sequence asks
whether one `κ_t` has almost invariant vectors.

## Role

- (G_aff) implies `thompson-t-euler-class-splits-over-almost-invariant-space` (MT), by the route
  `thompson-t-euler-splitting-via-affine-dirichlet-gaussian`. So it implies the Haagerup property
  of `T̄`, through `lifted-thompson-t-a-t-menable-via-measurable-euler-splitting`.
- It is sufficient only. Its failure refutes nothing about (MT) or `T̄`.

## Forced shape (established)

Let `(t_n, ξ_n)` be any witness.

- (A1) *Not through `κ₀`.* If `t_n → 0`, then `(ξ_n)` has no norm-convergent subsequence.
  - *Proof.* Suppose `ξ_{n_k} → ξ`. Then `‖ξ‖ = 1`.
  - The map `v ↦ κ(τ_v)` is strongly continuous from the Cameron–Martin space `H` to the unitaries.
    This is the Weyl representation, and it is standard.
  - `t_n c(g) → 0` in `H`, so `κ_{t_{n_k}}(g) → κ₀(g)` strongly.
  - For unitaries, strong convergence is uniform on norm-convergent sequences. So
    `κ₀(g)ξ = lim κ_{t_{n_k}}(g)ξ_{n_k} = lim ξ_{n_k} = ξ` for every `g`.
  - That contradicts `thompson-t-linear-gaussian-koopman-has-spectral-gap`, Theorem B.4: `κ₀` has
    no almost invariant vectors, so no invariant unit vector. ∎
  - In particular, rescaling one fixed vector as `t → 0`, which is part 3 of the splitting lemma,
    is dead.
- (A2) *The translation part is unbounded on `PSL_2(Z)`.* By
  `thompson-t-linear-gaussian-koopman-has-spectral-gap`, B.5, `‖c(P^n)‖ → ∞` for `P(x) = x + 1`.
  So the argument that killed `κ₀`, which is spectral gap of the Moebius part together with a
  vacuum defect, does not see `κ_t` for `t ≠ 0`.
- (A3) *Heavy tails.* The splitting over `X_{t_n}` is
  `β_{t_n}(σ(g)z^k, x) = −t_n^{-1} ℓ_{w(g)}(x) + β₀(g) + k` (here `a = −1`). By
  `perfect-extension-splittings-are-not-uniformly-integrable`, there is no subsequence along which
  every Gaussian linear functional `t_n^{-1} ℓ_{w(g)}` is uniformly integrable for the measures
  `ξ_n² γ`.
  - For example, `sup_n t_n^{-2} ∫ ℓ_{w(g)}² ξ_n² dγ < ∞` for all `g` is impossible.
  - In particular, `(ξ_n)` cannot be bounded in `L^∞` if `|t_n|` is bounded below.
- (A4) *Asymptotic freeness.* By `thompson-t-euler-splitting-witnesses-are-asymptotically-free`,
  `∫_{Fix(A^{t_n}_g)} ξ_n² dγ → 0` for every `g ≠ e`.

## Remarks (not established)

- *Coherent vectors fail uniformly, sketch only.* Consider `ξ = κ(τ_v)1` (shifted vacua), or
  shifts of the vacuum of a squeezed Gaussian.
  - Then `⟨κ_t(g)ξ, ξ⟩` is a Gaussian overlap. Its modulus is the Hellinger affinity of two
    Gaussian measures with covariances `1` and `ρ(g)ρ(g)^*`, times a factor `≤ 1` coming from the
    mean shift.
  - So `|⟨κ_t(g_0)ξ, ξ⟩| ≤ ⟨κ₀(g_0)1, 1⟩ < 1` uniformly in `t` and `v`, with `g_0` the
    non-Moebius element of B.3.
  - Witnesses must therefore be genuinely non-Gaussian vectors, such as superpositions of many
    coherent states, or Gaussian vectors with covariance adapted to `ρ(g_0)`, which are then
    moved by `PSL_2(Z)`.
- *Where to look.* On `PSL_2(Z)` alone, `κ_t` is the Koopman representation of an orthogonal
  affine Gaussian action with an unbounded cocycle. Here `⟨κ_t(g)1, 1⟩ = exp(−t²‖c(g)‖²/8)`, and
  `PSL_2(Z)` is Haagerup, so it poses no obstruction by itself.
  - The question is whether the vacuum defect of `g_0` can be spread against the translations
    `t c(g)`, which move mass off to infinity.
  - A quantitative form: find `ξ` with `‖κ_t(g)ξ − ξ‖ < ε` for `g` in the generating set
    `{A, B, C}` of `T` (Cannon–Floyd–Parry), for some `t`.
- *Possible kill.* A uniform lower bound
  `max_{g ∈ F} ‖κ_t(g)ξ − ξ‖ ≥ ε‖ξ‖` over all `t` would kill (G_aff).
  - This would be a relative spectral gap for the affine family. It could come from an
    `L²`-rigidity argument for `F_A × F_B` in the spirit of
    `thompson-t-bernoulli-euler-splittings-need-amenable-f`.
  - That kill needs `F` nonamenable, or a model-specific substitute. Not attempted.

## Attempts

- 2026-09-19 (swarm-0917-w14-w14-nv-follow, operator-algebras): isolated as the single remaining
  hole of the Dirichlet Gaussian route to (MT), after the linear case was killed
  (`thompson-t-linear-gaussian-koopman-has-spectral-gap`). Forced shape (A1)–(A4) recorded. Not
  decided.
