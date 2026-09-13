---
rg: 2
id: sl3z-cocompact-not-factor-of-bernoulli-times-profinite-proof
kind: route
title: Pull back the coupling cocycle, untwist it by Popa then Ioana, kill the holonomy by Bass-Milnor-Serre, and get an invariant probability on SL3(R)
target: sl3z-cocompact-not-factor-of-bernoulli-times-profinite
requires:
  - popa-bernoulli-product-cocycles-come-from-cofactor
  - ioana-profinite-cocycle-superrigidity
  - bms-sln-z-representations-agree-with-algebraic-ones
---

Notation: `G = SL_3(R)`, `Γ = SL_3(Z)`, `X = G/Λ` with (R), and `Y = s × p` with measure `μ`.

**0. Coupling cocycle.** Fix a Borel section `x ↦ g_x ∈ G` with `g_xΛ = x`, and put
`c(γ, x) = g_(γx)^(−1) γ g_x`. Then `c(γ, x) ∈ Λ`, and `g_(γx) c(γ, x) = γ g_x`. Also
`c(γ_1γ_2, x) = c(γ_1, γ_2x) c(γ_2, x)`, which is the cocycle convention of both imports.

**1. Pull back.** Suppose `Ψ : Y → X` is equivariant almost everywhere. Then `w(γ, z) = c(γ, Ψ(z))` is a
measurable cocycle for `s × p` with values in the countable group `Λ`.

**2. Popa.** By `popa-bernoulli-product-cocycles-come-from-cofactor`, `w` is cohomologous to
`(γ, (b, q)) ↦ v(γ, q)` for a cocycle `v` of `p`.

**3. Ioana.** By `ioana-profinite-cocycle-superrigidity`, `v` is cohomologous to `v''∘(id × r_n)` for some
level `n` and a cocycle `v''` over the finite transitive action on `X_n`. Composing the two cohomologies
(the second pulled back along the projection `Y → p`) gives a measurable `φ : Y → Λ` with
`w(γ, z) = φ(γz) v''(γ, r_n(q(z))) φ(z)^(−1)` for all `γ` and a.e. `z`.

**4. Holonomy.** Fix `a ∈ X_n` with stabilizer `Γ_a`, which has finite index. The map `ρ(δ) = v''(δ, a)`
is a homomorphism `Γ_a → Λ`, by the cocycle identity at the fixed point `a`.

**5. Finite image.** By `bms-sln-z-representations-agree-with-algebraic-ones`, applied to
`ι∘ρ : Γ_a → GL_m(Q)`, there is an algebraic homomorphism `F : SL_3 → GL_m` over `Q` with `F = ι∘ρ` on
some finite-index `Γ' <= Γ_a`. The kernel of `F` is a normal algebraic subgroup of the almost simple group
`SL_3`, so it is either `SL_3` or contained in the centre `μ_3`. Pigeonhole on the cosets `e_12^k Γ'` gives
`e_12^N ∈ Γ'` for some `N >= 1`. If `F` were nontrivial, `F(e_12^N)` would be unipotent, because algebraic
homomorphisms preserve unipotency, and nontrivial, because `e_12^N` is not central. Then
`ι(ρ(e_12^N))` would be a nontrivial unipotent matrix in `ι(Λ)`, contradicting (R). So `F` is trivial,
`ι∘ρ = 1` on `Γ'`, and `ρ = 1` on `Γ'` because `ι` is faithful. Hence `Γ_1 = ker ρ` has finite index in `Γ`.

**6. Trivial cocycle on a piece.** `Y_a = (r_n∘q)^(−1)(a)` has measure `1/|X_n|` and is invariant under
`Γ_1 <= Γ_a`. For `δ ∈ Γ_1` and a.e. `z ∈ Y_a`, `v''(δ, r_n(q(z))) = ρ(δ) = 1`, so
`c(δ, Ψ(z)) = w(δ, z) = φ(δz) φ(z)^(−1)`.

**7. Equivariant map into `G`.** Put `Ψ̃(z) = g_(Ψ(z)) φ(z)`. For `δ ∈ Γ_1` and a.e. `z ∈ Y_a`,

```text
Ψ̃(δz) = g_(δΨ(z)) φ(δz) = g_(δΨ(z)) c(δ, Ψ(z)) φ(z) = δ g_(Ψ(z)) φ(z) = δ Ψ̃(z).
```

**8. Properness.** `ν = Ψ̃_*(|X_n| · μ|_(Y_a))` is a Borel probability measure on `G`, invariant under left
multiplication by `Γ_1`. `Γ_1` is infinite and discrete, so it acts freely and properly on `G` and has a
Borel fundamental domain `D`, with `G = ⊔_(δ ∈ Γ_1) δD`. Then `1 = ν(G) = Σ_δ ν(δD) = Σ_δ ν(D)`, which is
`0` or `∞`. Contradiction. ∎

**Corollaries.** (1) A map from `s`, from `p`, or from `s × p × ι` composes with a projection, or restricts
to almost every slice `s × p × {t}` by Fubini, to give a map from `s × p`. (2) Steps 5--8 use only this: on
some finite-index `Γ_a` and some `Γ_a`-invariant piece of positive measure, the pulled-back cocycle is
cohomologous to a homomorphism `Γ_a → Λ`.
