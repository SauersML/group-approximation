---
rg: 2
id: hyperseries-conjugators-put-commutator-roots-in-h-proof
kind: route
title: Normalise one positive element to x + 1 by its Abel function; a conjugator of the wrong sign would make x minus the normaliser a positive infinite series that shifting by 1 decreases, against monotonicity; so outward conjugators lie below x and the letters of G(K; 1, ±1) keep one sign up the tower
target: hyperseries-conjugators-put-commutator-roots-in-h
requires:
  - edge-injective-quotients-give-hughes-free-division-rings
  - vertex-injective-quotients-give-hughes-free-division-rings
  - commutator-root-frontier-kills-pl-and-bi-ordered-targets
---

## Facts used from Bagayoko (arXiv:2509.09186)

Write `Γ = L̃^{>ℝ}` for the positive infinite finitely nested hyperseries, `T = x + 1` and `T_s = x + s` for
`s ∈ ℝ`. Products in `Γ` are compositions.
- **(B1) Bi-order.** `(Γ, ∘, x, <)` is a bi-ordered group, where `<` is the order of the field `L̃` (Thm. 1 =
  Cor. 3.18, Prop. 4.3 with Remark 4.2). Right invariance is Lemma 3.2 and left invariance is monotonicity.
- **(B2) Compatibility.** For `h ∈ Γ`, the map `f ↦ f ∘ h` is a strongly linear morphism of ordered rings of `L̃`
  (Def. 2.18). So it is strictly increasing and fixes `ℝ`, and `(f + r) ∘ h = f ∘ h + r` for `r ∈ ℝ`.
- **(B3) Abel functions.** For every `f ∈ Γ` with `f > x` there is `V ∈ Γ` with `V ∘ f = V + 1 = T ∘ V`, so
  `f = V^{-1} ∘ T ∘ V` (Thm. 4.6, applicable to `L̃` by Lemma 3.17 and Cor. 4.21).
- **(B4) Centraliser.** `C(T) = {T_s : s ∈ ℝ}` (Cor. 4.26). Only the inclusion `⊇` is needed below. It is
  immediate.

## Item 1

Let `x < A < B`, with Abel functions `V_A`, `V_B` from (B3). Put `W = V_A ∘ V_B^{-1} ∈ Γ`, so `V_A = W ∘ V_B` and
`A = V_B^{-1} ∘ W^{-1} ∘ T ∘ W ∘ V_B`.

**Step 1: `W T > T W`.** We have `B = V_B^{-1} T V_B` and `A = V_B^{-1} (W^{-1} T W) V_B`. Conjugation preserves a
bi-order, so `A < B` gives `W^{-1} T W < T`. Multiplying on the left by `W` gives `T W < W T`.

**Step 2: `V_A - V_B` is bounded below by a real.** Suppose instead that `V_A - V_B < r` for every `r ∈ ℝ`.
- By (B2), `(W - x) ∘ V_B = W ∘ V_B - V_B = V_A - V_B`, and `∘ V_B` is strictly increasing and fixes `ℝ`. So
  `W - x < r` for every real `r`.
- Then `ψ := x - W` is positive infinite, so `ψ ∈ Γ`. In `Γ` we have `x < T`, so left invariance (B1) gives
  `ψ ∘ x < ψ ∘ T`, that is, `ψ < ψ ∘ T`.
- Now compute with (B2):
  - `W ∘ T = (x - ψ) ∘ T = x + 1 - ψ ∘ T`;
  - `T ∘ W = W + 1 = x + 1 - ψ`.
- So `W T - T W = ψ - ψ ∘ T < 0`, which contradicts Step 1.

Hence there is `r ∈ ℝ` with `V_A - V_B ≥ r`.

**Step 3: the conjugators.** For `s ∈ ℝ` put `c_s = V_A^{-1} ∘ (V_B + s)`. Here `V_B + s ∈ Γ`, so `c_s ∈ Γ`.
- **It conjugates.** Using `T_s T = T T_s`, (B2) and `V_B ∘ B = V_B + 1`:
  - `A ∘ c_s = V_A^{-1} ∘ T ∘ (V_B + s) = V_A^{-1} ∘ (V_B + s + 1)`;
  - `c_s ∘ B = V_A^{-1} ∘ ((V_B ∘ B) + s) = V_A^{-1} ∘ (V_B + 1 + s)`.
- **Its sign.** Multiply on the left by `V_A` (B1): `c_s < x` if and only if `V_B + s < V_A`. This holds for every
  `s < r`.
- **There are no others.** If `A c = c B`, then `V_A c V_B^{-1}` commutes with `T`. By (B4) it is some `T_s`, so
  `c = c_s`.

**Mirror form.** Let `b < a < x`. Put `A = a^{-1}` and `B = b^{-1}`. Inversion reverses a bi-order, so
`x < A < B`. Take `c < x` with `A c = c B`. Inverting gives `c^{-1} a^{-1} = b^{-1} c^{-1}`, hence `a c = c b`. ∎

## Item 2

By item 2 of [[commutator-root-frontier-kills-pl-and-bi-ordered-targets]], the segments form a tower of cyclic
HNN extensions over the free group `N_[0,1] = <y_0, y_1>`.
- For `α = 1` the relation shifted by `n - 1` is `y_n^K = y_{n-1}^{-1} y_{n+1}^{-β} y_{n-1} y_{n+1}^β`, so
  `N_[0,n+1]` is `N_[0,n]` with a stable letter `u = y_{n+1}^β` and the one relation `u^{-1} y_{n-1} u = y_{n-1} y_n^K`.
- Hence a homomorphism `φ_n: N_[0,n] → Γ` extends to `N_[0,n+1]` as soon as some `c ∈ Γ` satisfies
  `φ(y_{n-1}) ∘ c = c ∘ φ(y_{n-1}) ∘ φ(y_n)^K`. The extension then sets `φ(y_{n+1}) = c^β`.

Let `ε = -β`. We show by induction on `n` that there is `φ_n` whose letters `φ(y_0), …, φ(y_n)` all lie on the side
`ε` of `x`: `> x` if `ε = 1`, `< x` if `ε = -1`.
- **Base, `n = 1`.** The group is free, so put `φ(y_0) = φ(y_1) = x + ε = x - β`.
- **Step.** Let `a = φ(y_{n-1})` and `b = a ∘ φ(y_n)^K`, with `K ≥ 1`.
  - If `ε = 1`, then `φ(y_n)^K > x`, and left invariance gives `b > a > x`. Item 1 with `(A, B) = (a, b)` gives
    `c < x` with `a c = c b`. Then `φ(y_{n+1}) = c^{-1} > x`, since `β = -1`.
  - If `ε = -1`, then `φ(y_n)^K < x`, so `b < a < x`. The mirror form gives `c < x` with `a c = c b`. Then
    `φ(y_{n+1}) = c < x`, since `β = 1`.

The `φ_n` are chosen compatibly, each extending the last, so their union is `φ: N_[0,∞) → Γ`. ∎

`hyperseries_first_steps.py` checks the two explicit steps for `K = 2, 3` exactly (sympy), together with the sign
of each new letter.

## Item 3

- `Q = φ(N_[0,∞))` is a countable subgroup of `Γ`. With the restricted order it is a bi-ordered group, so
  `Q ∈ 𝓗` (item 1 of [[vertex-injective-quotients-give-hughes-free-division-rings]]).
- Every `φ(y_i) ≠ x` and `Q` is torsion-free, so `φ` is injective on each edge group `<y_{n-1}>`, and so on the
  isomorphic edge `<y_{n-1} y_n^K>`.
- By induction `N_[0,n] ∈ 𝓗`:
  - the base is free;
  - at each step, `N_[0,n+1]` is an HNN extension with vertex group `N_[0,n] ∈ 𝓗`, and `φ|N_[0,n+1]` is injective
    on its edge group. Item 1 of [[edge-injective-quotients-give-hughes-free-division-rings]] applies.
- Conjugation by `t^m` in `G` maps `y_i` to `y_{i-m}`, so it maps `N_[0,m+n]` isomorphically onto `N_[-m,n]`.
  Hence every `N_[-m,m] ∈ 𝓗`.
- `N = ⋃_m N_[-m,m]` is a directed union, and `G = N ⋊ <t>` with `<t> ≅ Z`. `𝓗` is closed under directed unions
  and extensions, and contains `Z`, so `G ∈ 𝓗`.
- Reversing `t` gives `G(K; α, β) ≅ G(K; -β, -α)`, so `G(K; -1, -1) ∈ 𝓗` too. ∎

## Items 4 and 5

**Item 4** is item 1 of [[commutator-root-frontier-kills-pl-and-bi-ordered-targets]] (its table) combined with
item 3.

**Item 5.** For `(α, β) = (-1, 1)` the relation reads `y_{n+1}^{-1} a y_{n+1} = b`, with
`a = y_{n-1}^{-1}` and `b = y_{n-1}^{-1} y_n^K`.
- Item 1 (or its mirror) applies when `φ(b)` is further from `x` than `φ(a)`, on the same side. Without size
  control this needs `φ(y_n)` on the side of `φ(a)`, which is opposite to `φ(y_{n-1})`. So the signs must alternate.
- Item 1 always returns `c < x`, and here `φ(y_{n+1}) = c`. So `φ(y_2), φ(y_3), …` all lie below `x`, which
  contradicts the alternation at `y_2, y_3`. The recursion stops, and this is not an obstruction by itself.
- It matches the generalized-torsion identity of
  [[commutator-root-minus-one-groups-have-generalized-torsion]], which lives in `N_[0,3]` and kills every
  bi-orderable target there.
