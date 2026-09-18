---
rg: 2
id: lodha-moore-groups-embed-in-lodha-circle-group-proof
kind: route
title: Double every element across the two halves of the Cantor set, conjugating by the digit flip on the second half, so that each percolating element pairs with its inverse
target: lodha-moore-groups-embed-in-lodha-circle-group
requires:
  - lodha-circle-group-is-finitely-presented-and-simple
  - lodha-circle-group-satisfies-pbh
---

The source is Y. Lodha, arXiv:1710.06220v2 (PDF read 2026-09-18, pp. 3–10 and 25–27). Maps act
on `2^N`, written as functions. For a prefix `σ` and a homeomorphism `h`, let `h_σ` be
`σξ ↦ σh(ξ)` on the cone `σ2^N`, and the identity elsewhere. Then:
- `h ↦ h_σ` is an injective homomorphism;
- `(h_σ)_τ = h_{τσ}`;
- maps transplanted to independent prefixes commute.

Lodha's `x_σ, y_σ` are `x_σ = (x)_σ` and `y_σ = (y)_σ`.

**1. The primitive maps (Lodha p. 5).**
- `x(00η) = 0η`, `x(01η) = 10η`, `x(1η) = 11η`.
- `y(00η) = 0y(η)`, `y(01η) = 10y^{-1}(η)`, `y(1η) = 11y(η)`.

Inverting the rules for `y` gives `y^{-1}(0ζ) = 00y^{-1}(ζ)`, `y^{-1}(10ζ) = 01y(ζ)` and
`y^{-1}(11ζ) = 1y^{-1}(ζ)`. These are Lodha's substitutions on p. 7.

**2. The flip.** Let `f` swap every digit, and write `ζ̃ = f(ζ)`. Then:
- **(a)** `f x f = x^{-1}`. Directly: `fxf(0η) = f(x(1η̃)) = 00η`,
  `fxf(10η) = f(x(01η̃)) = 01η` and `fxf(11η) = f(x(00η̃)) = 1η`. These are the rules of `x^{-1}`.
- **(b)** `f y f = y^{-1}`. Put `z = fyf`. The same computation gives:
  - `z(0η) = 00z(η)`;
  - `z(10η) = 01z^{-1}(η)`, using `f y^{-1} f = z^{-1}`;
  - `z(11η) = 1z(η)`.

  So the pairs `(z, z^{-1})` and `(y^{-1}, y)` satisfy the same system of rules:

  ```text
  h(0η) = 00h(η),   h(10η) = 01k(η),   h(11η) = 1h(η),
  k(00η) = 0k(η),   k(01η) = 10h(η),   k(1η) = 11k(η).
  ```

  Every rule reads at most two leading letters, emits at least one letter, and continues with
  `h` or `k` on the tail. By induction on `n`, the first `n` letters of `h(ξ)` and `k(ξ)` are
  determined for every `ξ`. So the system has at most one solution, and `z = y^{-1}`.
- **(c)** `f h_σ f = (fhf)_{σ̃}`. Directly: `f h_σ f(σ̃ξ) = f(σh(ξ̃)) = σ̃(fhf)(ξ)`, and both sides
  are the identity off `σ̃2^N`. So `f x_σ f = x_{σ̃}^{-1}` and `f y_σ f = y_{σ̃}^{-1}`.

**3. The double.** Put `ψ(h) = h_0 · (f h f)_1`.
- `h ↦ h_0` and `h ↦ (fhf)_1` are homomorphisms whose images commute, so `ψ` is a homomorphism
  `Homeo(2^N) → Homeo(2^N)`.
- `ψ(h)` restricted to the cone `0` is a copy of `h`, so `ψ` is injective.

On the generators of `𝒢`, using 2(c):

```text
ψ(x_σ) = x_{0σ} · x_{1σ̃}^{-1},        ψ(y_σ) = y_{0σ} · y_{1σ̃}^{-1} = w_{0σ, 1σ̃}.
```

- **The `x` images.** Every `x_τ` lies in `F ≤ T ≤ S`. It is an `x`-generator in Lodha's
  generating set `𝒳` for `S` (p. 10, item 2).
- **The `y` images.** The prefixes `0σ` and `1σ̃` are independent. Lodha's Lemma 3.1 (p. 9)
  states: "For each pair σ, τ of independent finite binary sequences, w_{σ,τ} ∈ S". Here
  `w_{σ,τ} = y_σ y_τ^{-1}`.

So `ψ(𝒢) ≤ S`. By `lodha-circle-group-is-finitely-presented-and-simple`, `S` is finitely
presented and simple, so every subgroup of `𝒢` embeds in a finitely presented simple group. With
`lodha-circle-group-satisfies-pbh`, every subgroup of `𝒢` is also in the permutational class.

**4. The real-line group `G`.**
- **The model.** Lodha p. 3 defines `G = ⟨F, c, d_1, d_2⟩`, with:
  - `c(t) = 2t/(1+t)` on `[0,1]`;
  - `d_1(t) = 2t` for `t ≥ 0`;
  - `d_2(t) = 2t` for `t ≤ 0`.

  His semiconjugacy is `Φ(0ξ) = −φ(ξ̃)` and `Φ(1ξ) = φ(ξ)`, with `φ(0ξ) = φ(ξ)/(1+φ(ξ))` and
  `φ(1ξ) = 1 + φ(ξ)` (p. 5).
- **The scaling identity.** Proposition 2.3, `Φ(ξ)·c = Φ(ξ·y_10)`, read on the cone `10` says:

  ```text
  φ(y(η))/(1 + φ(y(η))) = c(φ(η)/(1 + φ(η))) = 2φ(η)/(1 + 2φ(η)).
  ```

  Since `t ↦ t/(1+t)` is injective, `φ(y(η)) = 2φ(η)`, and so `φ(y^{-1}(η)) = φ(η)/2`.
- **The dilations.** From the scaling identity:
  - `Φ(1y(η)) = 2Φ(1η)`, so `y_1` induces `d_1`;
  - `Φ(0y^{-1}(ξ)) = −φ(y(ξ̃)) = 2Φ(0ξ)`, using 2(b), so `y_0^{-1}` induces `d_2`.
- **The comparison map.** With Proposition 2.3 for `a ↔ x` and `b ↔ x_1`, this gives a surjection
  `⟨x, x_1, y_10, y_1, y_0⟩ → G`.
- **Injectivity.**
  - `φ` is order-preserving and continuous from `2^N` (lexicographic order) onto `[0,∞]`.
  - On a cone `s2^N`, `φ = M_s ∘ φ` for an injective Möbius map `M_s`, and `φ(0^∞) = 0 ≠ ∞ = φ(1^∞)`.
    So `φ` is constant on no cone.
  - So each fibre of `Φ` is an order-convex set with empty interior. It is a point or the two
    endpoints of a gap, and there are countably many gaps.
  - Hence the points with singleton fibre are dense in `2^N`. An element inducing the identity on
    `R ∪ {∞}` fixes all of them, so it is trivial.

  So `G ≅ ⟨x, x_1, y_10, y_1, y_0⟩ ≤ 𝒢`.

**5. Part 1** is Lodha's Lemma 5.2. It is also a special case of step 3, since `G_0 ≤ 𝒢`. ∎
