---
rg: 2
id: lifted-thompson-t-farey-fock-twist-bound
kind: claim
title: "In the Farey model Thompson's T acts on H^{1/2}(S^1)/R through the restricted symplectic group, and the Weyl-twisted Fock representations give c(t/4π)² ≤ 3(K²t² + 2B²|t|(1+n) + δ) for every Fock density with mean particle number n and Ad-defect δ; so Bekka amenability of the Farey–Fock representation of T refutes relative (T) of the centre of T-bar, a subexponential particle-number profile gives Haagerup for T-bar, and without Bekka amenability the whole Weyl-twisted Fock family has twist cost bounded below"
distinct_from:
  lifted-thompson-t-root-twist-cost-iff-euler-cup-product: that turns an orthogonal cup-product representative of e_R into twist costs O(√θ); this needs no invariant Hilbert structure, only almost invariant density matrices in one fixed Fock representation, and gives slower rates
  lifted-thompson-t-euler-class-in-kahler-subspace: that is (K), an exact invariant unitary structure; this is an approximate (amenability) version inside a concrete representation, and does not decide (K)
  lifted-thompson-t-haagerup-iff-twist-cost-spectral-measure: that reduces Haagerup for T-bar to the size of c; this bounds c from above by an explicit functional of one representation of T
  thompson-t-euler-class-splits-over-almost-invariant-space: that asks for a nonsingular T-space with a measurable splitting; this uses a non-commutative (Fock) space and no splitting
artifacts: []
---

**ESTABLISHED** by `lifted-thompson-t-farey-fock-twist-bound-proof`, modulo three classical
analytic imports, which are recalled with references and not re-derived: Shale's
implementability theorem, the Nag–Sullivan boundedness of composition operators on
`H^{1/2}(S^1)/R`, and the Weil–Petersson criterion (a quasisymmetric map `h` has `C_h ∈ Sp_res`
iff `log h'` lies in `H^{1/2}`; Takhtajan–Teo, and Shen, Amer. J. Math. 2018).

## Notation

- `T̄`, `z`, `S`, `e(θ)` and the twist cost `c` are as in
  `lifted-thompson-t-relative-t-forces-dyadic-twist-gap`.
- Realize `T` as `PPSL_2(Z)` acting on `RP^1 ≅ R/Z`, using `thompson-t-is-isomorphic-to-ppsl2z`.
  `T̄` is its lift to `R`, and `z(x) = x + 1`.
- `H = H^{1/2}(R/Z; R)/R` is a real Hilbert space. It carries:
  - the symplectic form `ω(φ, ψ) = ∫_0^1 φ dψ`;
  - the Hilbert-transform complex structure `J_0`.
  `F` is the boson Fock space over `(H, J_0)`, with Weyl operators `W(f) = e^{iΦ(f)}`, the
  relation `W(f)W(k) = e^{−iω(f,k)/2} W(f + k)`, and the number operator `N`.
- `T` acts on `H` on the left by `g·φ = φ ∘ g̃^{-1}`. The *displacement cocycle*
  `b_g = id − g̃^{-1}` is a 1-cocycle of `T` into `H`.
- For a density matrix `ρ` on `F`, the quantities are:
  - `n(ρ) = Tr(ρN) ∈ [0, ∞]`;
  - `δ(ρ) = max_{s∈S} ‖M(s)ρM(s)^* − ρ‖_1`.
- `δ_* = inf_ρ δ(ρ)`.
- `A(η) = inf{ n(ρ) : δ(ρ) ≤ η }`, the *particle-number profile*.

## Statement

- **(W) Farey regularity.** Every `g ∈ PPSL_2(Z)` is `C^1` on the circle, and `log g'` is
  Lipschitz. The reason is that at a breakpoint `p`, the two Möbius pieces differ by an element of
  the cusp stabilizer of `p` in `PSL_2(Z)`, and that element is parabolic.
  - Hence (imports) each `g` acts on `H` by a bounded symplectic operator in `Sp_res`, and there
    is a projective unitary representation `M` of `T` on `F` (the *Farey–Fock representation*)
    with `M(g)W(f)M(g)^* = W(g·f)`.
  - `b_g ∈ H` for every `g`.
  - `PSL_2(Z) ≤ T` acts by Möbius maps, so it fixes the vacuum ray.
- **(1) Twist bound.** Put `B = max_{s∈S} ‖b_{p(s)}‖`. Then there is a constant `K = K_S` such
  that, for every `t ∈ R` and every density `ρ` with `n(ρ) < ∞`,
  `c(t/4π) ≤ K|t| + B·√(2|t|(1 + n(ρ))) + δ(ρ)^{1/2}`.
  The witness representation is `ρ_t = (phase)·W(√t b)M ⊗ M̄` on `HS(F) ≅ F ⊗ F̄`, with
  `ρ_t(z) = e^{it/2}`, and the witness vector is `ρ^{1/2}`.
- **(2) Necessity (class kill).** For every `t` and every unit vector `ξ ∈ HS(F)`,
  `max_{s∈S} ‖ρ_t(s)ξ − ξ‖ ≥ δ(ξ^*ξ)/2 ≥ δ_*/2`.
- **(3) Consequences.**
  - (a) If `M|_T` is Bekka-amenable, i.e. `δ_* = 0`, then `c(θ) → 0` as `θ → 0`. By part (c) of
    `lifted-thompson-t-relative-t-forces-dyadic-twist-gap`, some cnd function on `T̄` is then
    unbounded on `⟨z⟩`, which refutes `lifted-thompson-t-center-has-relative-t`.
  - (b) If `A(η) ≤ exp(η^{−1+ε})` for some `ε > 0` and all small `η`, then
    `Σ_k c(2^{−k})² < ∞`. So `T̄` is Haagerup by (B) of
    `lifted-thompson-t-haagerup-iff-twist-cost-spectral-measure`, and
    `lifted-thompson-t-is-a-t-menable` holds.
  - (c) If `δ_* > 0`, every Weyl-twisted Farey–Fock representation `ρ_t`, and more generally every
    `V ⊗ M̄` with `V` any projective representation of `T̄` whose multiplier matches, has all
    vectors at defect `≥ δ_*/2`. The whole family then gives nothing, uniformly in `t`.
    - Invariant: the Bekka defect `δ_*` of `M|_T`.
    - Step where it dies: the density matrix `ξ^*ξ` of an almost invariant `ξ`.

## Role (new decomposition)

- It gives a concrete two-level target inside one explicit representation of Thompson's `T`, the
  Farey–Fock representation `M`:
  - (Q1) *Is `M|_T` Bekka-amenable?* A yes refutes `lifted-thompson-t-center-has-relative-t`, and
    with it the refutation route through `cantor-integer-maps-central-direction-has-relative-t`.
    A no kills the metaplectic lead recorded under `lifted-thompson-t-euler-class-in-kahler-subspace`
    (Attempts, w13 spark) and every twist family of the form `V ⊗ M̄`.
  - (Q2) *How fast does the particle-number profile `A(η)` grow?* Subexponential growth in `1/η`
    proves `lifted-thompson-t-is-a-t-menable`, which is necessary for
    `brin-thompson-groups-nv-are-a-t-menable`.
- An exactly invariant state on `B(F)` with finite field second moments would give
  `c = O(√θ)`, which is the (K) rate of `lifted-thompson-t-root-twist-cost-iff-euler-cup-product`.
  Almost invariance with a controlled second moment is the approximate version of (K).
- The Farey model removes the need for Ghys–Sergiescu smoothing. It also explains the w13 obstacle:
  in the dyadic PL model `log g'` jumps, so `g ∉ Sp_res`. In the Farey model the breakpoints are
  cusps, so `log g'` only has kinks.

## Not claimed

- Whether `M|_T` is Bekka-amenable. The subgroup `PSL_2(Z)` fixes the vacuum, so no obstruction
  comes from it. A kill of (Q1) would need a non-amenable `Λ ≤ T` with `M|_Λ` weakly contained in
  the `σ`-twisted regular representation of `Λ`.
- Any bound on `A(η)`.
- (K) itself, and any statement about the Godbillon–Vey part of the metaplectic multiplier. That
  multiplier is cancelled by `M̄`, so it plays no role here.
- The analytic imports in (W) are recalled, not re-derived. Only the regularity (`C^1`, Lipschitz
  `log g'`) is proved here.
