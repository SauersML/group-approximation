---
rg: 2
id: artin-groups-embed-in-decorated-garside-odometer-groups
kind: claim
title: Every finite-type Artin group with at least two generators embeds in the type F_infinity full group of its decorated Garside odometer category
requires:
  - decorated-garside-odometer-full-groups-are-type-f-infinity
distinct_from:
  artin-normal-form-boundary-full-groups-fix-a-point: that is about the Deligne boundary, where the Artin group has two global fixed points; this lifts the action to a compact space with no fixed points, where every element is locally a groupoid germ.
  spherical-artin-groups-satisfy-boone-higman: that is Boone--Higman for these groups, on main only through the characteristic-zero linear route; this gives a finitely presented (F_infinity) Thompson-like overgroup, and simplicity is still open.
artifacts:
  - research/artifacts/gq-bh-bh-free-15-2026-preprints.md
---

**ESTABLISHED** (lane proof, not reviewed; no priority claimed). One input is
imported from Belk--Bleak--Chatterji--Matucci--Perego (preliminary 2026,
Theorem 2.4): the finite-type Artin group `A` acts faithfully on its Deligne
normal-form boundary `∂L`. That also needs the identification checked below.

## Setting

- `P = A^+` is the positive Artin monoid, with Garside element `Δ` and word length
  `ℓ`.
- `C`, `D = C ⋈ Z`, `F_P` and the odometer `τ` are as in
  `decorated-garside-odometer-full-groups-are-type-f-infinity`.
- `X = ∂Ω_D`, which is homeomorphic to `Ξ × C_L × C_2`, where:
  - `Ξ = ∂Ω_{C_P}` consists of Garside boundary points `ξ ∈ ∂Ω_P`, each with a
    decoration `y ∈ {0,1}^N`;
  - `C_L` and `C_2` are the two free binary factors.
- `P_2 = ∂Ω_P ∖ Δ^2∂Ω_P` is clopen.
- `Y ⊆ X` is the clopen set of points whose Garside coordinate lies in `P_2`.

## Statement

There is an injective homomorphism `A → F_P`. Each image element is supported
in `Y`.

## Proof

1. **An action of `A` on `P_2 × Z`.**
   - For `g ∈ A`, pick `k ≥ 0` with `x_g = Δ^{2k} g ∈ A^+`.
   - For `ξ ∈ P_2`, write `x_g ξ = Δ^{2j} ξ'` with `ξ' ∈ P_2` and `j ≥ 0`. This is
     unique, since `∂Ω_P = ⊔_j Δ^{2j} P_2 ⊔ {Δ^∞}`. Also `x_g ξ ≠ Δ^∞`, because
     `x Δ^∞ = Δ^∞` and `λ_x` is injective.
   - Set `g·(ξ, m) = (ξ', m + j − k)`. The value does not depend on `k`, and this
     is an action, because `Δ^2` is central.
   - The map `(ξ, m) ↦ Δ^{2m} ξ` identifies `P_2 × Z` equivariantly with
     `∂L ∖ {Δ^{±∞}}`: Deligne normal forms are `Δ^{-j} w` or positive words.
   - Hence the action is faithful, by BBCMP Theorem 2.4 and density.
2. **Local form.**
   - On each piece where `j` is constant, `ξ ↦ ξ'` is the `I_l(P)`-germ
     `λ_{Δ^{2j}}^{-1} λ_{x_g}`.
   - `j` is locally constant, since the sets `Δ^{2j}∂Ω` are clopen.
   - `j` is bounded on `P_2`: `x_g P_2` is compact and misses `Δ^∞`, so it misses
     some neighbourhood `Δ^{2J}∂Ω` of `Δ^∞`.
   - So there are finitely many pieces, and on each, `c = j − k` and
     `κ = ℓ(x_g) − 2jℓ(Δ) = ℓ(g) − 2cℓ(Δ)` are constant.
3. **The lift to `Y`.**
   - Let `z ∈ {0,1}^Z` be the two-sided sequence whose right half `z_0 z_1 ⋯` is
     the decoration `y` of `ξ`, and whose left half `z_{-1} z_{-2} ⋯` is the `C_L`
     coordinate.
   - Put `Φ_g(ξ, y, x, x_2) = (ξ', y', x', τ^c x_2)`, where `(y', x')` is read off
     from `σ^κ z` and `σ` is the right shift.
   - This is the conjugate of the action
     `g·(ξ, m, z) = (ξ', m + c, σ^{ℓ(g) − 2cℓ(Δ)} z)` on `P_2 × Z × {0,1}^Z`, with
     the `Z` coordinate completed to the 2-adic odometer `C_2 ≅ Z_2`.
   - The uncompleted formula is an action: it is `g·(Δ^{2m}ξ, z) = (gΔ^{2m}ξ, σ^{ℓ(g)} z)`
     rewritten in coordinates, and `ℓ : A → Z` is a homomorphism.
   - The completion is still an action, because `c` is a locally constant
     cocycle.
   - So `g ↦ Φ_g` is a homomorphism into `Homeo(Y)`. It is injective, because it
     covers the faithful action on `P_2 × Z`, which is dense.
4. **Each `Φ_g` is piecewise a `D`-germ.**
   - On a piece with constants `(j, c, κ)` and `κ ≥ 0`, `Φ_g` is the composite of
     four moves:
     1. Remove the first `ℓ(x_g)` digits `v_1` of `C_L`.
     2. Prefix `(x_g, reverse(v_1))` to the decorated Garside coordinate.
     3. Remove the decorated prefix `(Δ^{2j}, w_2)` and push `reverse(w_2)` back onto `C_L`.
     4. Apply `a^c` on `C_2`.
   - Each move is an element of `I_l(C)` or of `Z`: a product of maps `λ_e` and
     their inverses, and `a^c` acting on the last factor only.
   - The case `κ < 0` is symmetric.
   - So `Φ_g` agrees locally with germs of `I_l(D) ⋉ ∂Ω_D`.
5. **Membership.** Extend `Φ_g` by the identity on `X ∖ Y`. The result is a
   homeomorphism of `X` that is locally given by groupoid germs, so it lies in
   `F_P`. ∎

## What a referee should check

- **Boundary identification.** Li's boundary `∂Ω_P` (maximal characters of
  constructible right ideals) should be identified with the space of infinite
  left-greedy normal forms, i.e. the positive part of BBCMP's `∂L`, in a way that
  is compatible with left multiplication. This is standard Garside theory, but it
  was not checked here against a written source.
- **Faithfulness.** It is imported from BBCMP Theorem 2.4, which holds for at
  least two Artin generators.
