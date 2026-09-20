---
rg: 2
id: thompson-t-euler-splitting-via-affine-dirichlet-gaussian
kind: route
title: "The Euler extension of T splits measurably over the disjoint union of the affine Gaussian spaces of the Dirichlet model (area class -e_R); almost invariant affine Koopman vectors on that union are exactly what is missing for (MT)"
target: thompson-t-euler-class-splits-over-almost-invariant-space
requires:
  - thompson-t-affine-dirichlet-koopman-almost-invariant
  - symplectic-gaussian-actions-split-area-cocycles
  - thompson-t-dirichlet-space-restricted-symplectic-model
---

**What this route does.** It reduces (MT) to one explicit almost-invariance question. The space
and the splitting are given, so only the Koopman vectors remain, and that is prerequisite 1,
(G_aff). The other two prerequisites are ESTABLISHED.

**Route.**
1. *Model.* `thompson-t-dirichlet-space-restricted-symplectic-model` gives
   `(T, E, H, ω, J, ρ, c)` with `ρ : T → Sp_res(H)`, a cocycle `c`, and area cocycle
   `Ω = −ε + dβ_A` for the extension `E` of lifts. So the setting of
   `symplectic-gaussian-actions-split-area-cocycles` holds with `a = −1` and `β₀ = β_A`.
2. *Spaces and splittings.* By parts 1 and 2 of the splitting lemma, for each `t ≠ 0` the affine
   action `A^t` of `T` on the conull set `X_t ⊆ X` is nonsingular. The splitting is
   `β_t(σ(g)z^k, x) = −t^{-1} ℓ_{w(g)}(x) + β_A(g) + k`.
   - It is measurable.
   - It satisfies `β_t(gh, x) = β_t(g, hx) + β_t(h, x)` everywhere.
   - It has `β_t(z, ·) = 1`.
3. *Union.* Take `t_n` and `ξ_n` from (G_aff). Let `W = ⊔_n X_{t_n}`, with the measure `γ` on
   each copy. This is a standard σ-finite space.
   - `T` acts on the `n`-th copy by `A^{t_n}`, nonsingularly, so `L²(W) = ⊕_n L²(X_{t_n}, γ)` and
     the Koopman representation is `⊕_n κ_{t_n}`. It uses the convention
     `(dg_*μ/dμ)^{1/2} ξ∘g^{-1}` of `central-extension-haagerup-from-measurable-euler-splitting`,
     the same as in the splitting lemma.
   - Put `ξ_n` in the `n`-th summand. These are almost invariant unit vectors.
   - Define `β = β_{t_n}` on the `n`-th copy. It is measurable, satisfies the cocycle identity, and
     has `β(z, ·) = 1`.
4. *From `E` to `T̄`.* By step 3 (Identification) of
   `thompson-t-dirichlet-space-restricted-symplectic-model-proof`, conjugation by a
   lift `k̃` of `k = ψ₀∘φ^{-1}` gives an isomorphism `θ : T̄ → E`.
   - `θ` covers the identification of the PL and smoothed copies of `T`.
   - It sends the central generator to `z^s`, `s = ±1`.
   - Put `β′(g̃, x) = s·β(θ(g̃), x)`. The cocycle identity is linear in `β` and preserved by
     composing with a homomorphism over `T`. Since `β(z^k, ·) = k`, `β′(z_{T̄}, ·) = s·s = 1`.
   - So `(W, β′)` is a witness for (MT). ∎

**Downstream.** Combined with `lifted-thompson-t-a-t-menable-via-measurable-euler-splitting`
(`central-extension-haagerup-from-measurable-euler-splitting` and Farley), this gives `T̄`
Haagerup. `T̄ ≤ 2V`, so that is a necessary piece of `brin-thompson-groups-nv-are-a-t-menable` at
`n = 2`.

**What is dead on this route.** Part 3 of the splitting lemma, which reaches almost invariance
through the linear representation `κ₀` by letting `t → 0`, never applies here. This is shown by
`thompson-t-linear-gaussian-koopman-has-spectral-gap`, which gives spectral gap of `PSL_2(Z)` on
the tempered chaos and a vacuum defect of the non-Moebius element `g_0`. The forced shape (A1) of
prerequisite 1 records what that leaves open.

**Attack order.**
1. Look for an explicit non-Gaussian `ξ`, a superposition of shifted squeezed states, with small
   defect on the three Cannon–Floyd–Parry generators for some fixed `t`. This can be tested
   numerically on finite Fourier truncations of `H`.
2. Try to refute: prove a uniform spectral-gap bound for `κ_t` over all `t`. That kills (G_aff),
   and with it this route, but not (MT).
