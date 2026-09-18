---
rg: 2
id: free-permutational-products-preserve-pbh-proof
kind: route
title: Send the factor at x to the transvections by g_x K g_x^(-1) with g_x = y δ_x y, where δ_x is a lamp of Z/2 wr_X W, and let W act by twisted conjugations
target: free-permutational-products-preserve-pbh
requires:
  - permutational-boone-higman-closed-under-wreath-products
  - boone-higman-type-a-class-closed-under-finite-extensions
  - fp-simple-highly-transitive-groups-satisfy-pbh
  - relative-automorphism-of-fp-simple-mif-group-has-type-a-action
  - type-a-action-gives-boone-higman-for-subgroups
---

Lane proof (bh-free-10, 2026-09-18), not reviewed. Automorphisms compose right to
left. The automorphisms `ρ_a`, `γ_c` and formula (GP1) are those of
`pbh-graph-product-closure-proof`; they are rechecked in Step 1.

## Part 1. The criterion

Assume `W, K ∈ B_A`, `X` is a countable `W`-set, and `Z/2 wr_X W ∈ B_A`.

**Step 0. One envelope.**
- `L = (Z/2 wr_X W) × K` lies in `B_A` by product closure
  (`boone-higman-type-a-class-closed-under-finite-extensions`). So `L <= E` for a
  group `E` with a type (A) action. `E` is finitely presented, hence finitely
  generated, and BFFHZ Theorem C, (i) ⟹ (iv)
  (`fp-simple-highly-transitive-groups-satisfy-pbh`), embeds `E` in a finitely
  presented simple MIF group `M`.
- Inside `M` we now have:
  - `W` and `K`, which commute;
  - lamps `δ_x` (`x ∈ X`), each of order 2, with `w δ_x w^(-1) = δ_(wx)`;
  - `δ_x δ_(x') != 1` for `x != x'`, because lamps at distinct points are independent
    in `(Z/2)^(X)`.

**Step 1. The actor and its elements.**
- Let `P = M * F(x, y)` and `Ω = Aut_M(P)`. By BFFHZ Theorem E with `n = 2`
  (`relative-automorphism-of-fp-simple-mif-group-has-type-a-action`), `Ω` admits an
  action of type (A), so every subgroup of `Ω` is in `B_A`.
- **Transvections.** For `a ∈ M * <y>`, `ρ_a` fixes `M` and `y` and sends `x -> x a`.
  Since `ρ_a` fixes `b`, `ρ_a ρ_b (x) = x a b`. So `a -> ρ_a` is a homomorphism, and it
  is injective because `ρ_a(x) = x a`.
- **Twisted conjugations.** For `m ∈ M`, `γ_m` fixes `M` and sends `x -> x m`,
  `y -> m^(-1) y m`. Then `γ_m γ_(m') = γ_(m m')`, so `m -> γ_m` is a homomorphism
  `M -> Ω`.
- **The automorphism `σ_m` of `M * <y>`.** It acts on `M` by conjugation by `m` and
  fixes `y`.
- **Formula (GP1).** `γ_m ρ_a γ_m^(-1) = ρ_(σ_m(a))` for `a ∈ M * <y>`. Both sides fix
  `M`. On `y`, the left side gives `γ_m(ρ_a(m y m^(-1))) = γ_m(m y m^(-1)) = y`. On `x`
  it gives `x -> x m^(-1) -> x a m^(-1) -> x m γ_m(a) m^(-1)`. Finally `m γ_m(a) m^(-1)`
  is `σ_m(a)`: both are homomorphisms of `a`, they agree on `M` (`γ_m` fixes `M`), and
  both fix `y` (`m (m^(-1) y m) m^(-1) = y`).

**Step 2. The homomorphism `Φ: K *_X W -> Ω`.**
- Put `g_x = y δ_x y ∈ M * <y>`. Then `σ_w(g_x) = y (w δ_x w^(-1)) y = g_(wx)`.
- Define `Φ(w) = γ_w` for `w ∈ W`, and `Φ(k_x) = ρ_(g_x k g_x^(-1))` for `k ∈ K`, where
  `k_x` is `k` in the factor at `x`.
  - `Φ` is a homomorphism on `W`, and on each factor `K_x`: conjugation by `g_x` is a
    homomorphism, and so is `ρ`.
  - The action relation `w k_x w^(-1) = k_(wx)` is preserved. By (GP1),
    `Φ(w) Φ(k_x) Φ(w)^(-1) = ρ_(σ_w(g_x k g_x^(-1))) = ρ_(g_(wx) (w k w^(-1)) g_(wx)^(-1))`,
    and `w k w^(-1) = k` because `W` and `K` commute in `M`. This is `Φ(k_(wx))`.
- These are all the defining relations of `K *_X W`, so `Φ` is a homomorphism.

**Step 3. Injectivity on the free part.**
- On `N = *_X K_x` we have `Φ = ρ ∘ ψ`, where `ψ(k_x) = g_x k g_x^(-1)`. Since `ρ` is
  injective, it suffices that `ψ` is injective.
- Take a reduced word `k^(1)_(x_1) ... k^(n)_(x_n)` with `n >= 1`, every `k^(i) != 1`,
  and `x_i != x_(i+1)`. Using `g_x^(-1) = y^(-1) δ_x y^(-1)`, its image is

```text
y δ_(x_1) y k^(1) y^(-1) (δ_(x_1) δ_(x_2)) y k^(2) y^(-1) (δ_(x_2) δ_(x_3)) y ... y k^(n) y^(-1) δ_(x_n) y^(-1).
```

- The syllables alternate between `M \ {1}` and `<y> \ {1}`. Every `δ_x` is nontrivial,
  every `k^(i)` is nontrivial, and every `δ_(x_i) δ_(x_(i+1))` is nontrivial by Step 0.
  So this is a reduced word of positive length in the free product `M * <y>`, and it is
  not `1`.

**Step 4. Injectivity.**
- Every element of `K *_X W` is `n w` with `n ∈ N` and `w ∈ W`, and
  `Φ(n w) = ρ_(ψ(n)) γ_w`.
- Suppose this is the identity. On `y` it gives `ρ_(ψ(n))(w^(-1) y w) = w^(-1) y w`,
  since `ρ` fixes `M` and `y`. So `w^(-1) y w = y` in `P`. A nontrivial element of the
  free factor `M` does not commute with `y`, so `w = 1`.
- Then `ρ_(ψ(n)) = id`, so `ψ(n) = 1`, and `n = 1` by Step 3.

So `K *_X W` embeds in `Ω` and lies in `B_A`. `∎`

## Part 2. Finite stabilizers

`Z/2 ∈ B_A`, because `Z/2 <= V` and `V` is finitely presented, simple and MIF (Theorem
C). If the stabilizers of `X` are finite, then `Z/2 wr_X W ∈ B_A` by
`permutational-boone-higman-closed-under-wreath-products`. Now apply Part 1. `∎`

## Part 3. Centralizing amalgams over finite `C`

Let `C <= W` be finite and `X = W/C`. Its stabilizers are the conjugates of `C`, which
are finite. `W *_C (C × K) ≅ K *_(W/C) W`, by the following mutually inverse
homomorphisms:
- **Forward.** `w -> w`, and `k_(wC) -> w k w^(-1)`. This is well defined, since `C`
  commutes with `K`. It respects `w' k_x w'^(-1) = k_(w'x)`.
- **Backward.** `w -> w`, and `k -> k_C`. It respects `[c, k] = 1`, because
  `c k_C c^(-1) = k_(cC) = k_C`.
- **The composites.** Both are the identity on generators: `k -> k`, and
  `k_(wC) -> w k_C w^(-1) = k_(wC)`.

So Part 2 applies. With `K = Z` this is the centralizing HNN extension. `∎`

## Part 4. Amalgams over finite `C`

- **⟸.** Identify `X, Y <= M ∈ B_A` with the same subgroup `C <= X ∩ Y`. By Part 3,
  `G_M = M *_C (C × <t>)` lies in `B_A`. It is the HNN extension of `M` with stable
  letter `t` centralizing `C`. Map `X *_C Y -> G_M` by `x -> x` and `y -> t y t^(-1)`.
  This is a homomorphism, since `t` fixes `C` and so the two maps agree on `C`.
  - Take a reduced alternating product of `n >= 2` letters from `X \ C` and `Y \ C`.
    Its image replaces each `Y`-letter `a` by `t a t^(-1)`.
  - A Britton pinch would be `t a t^(-1)` with `a ∈ C`, or `t^(-1) b t` with `b ∈ C`,
    where `b` is an `X`-letter between two `Y`-letters. Neither occurs.
  - So the image contains `t` and is not `1` by Britton's lemma. Single letters are
    nontrivial already.
  - So the map is injective, and `X *_C Y ∈ B_A`.
- **⟹.** Take `M = X *_C Y`.
- **Doubles.** Take `M = X` with both embeddings the identity. `∎`

## Part 5. HNN extensions over finite subgroups

- **⟸.** Let `W <= M ∈ B_A` and `s ∈ M` with `s c s^(-1) = θ(c)` for `c ∈ C_1`. Put
  `G_M = M *_(C_2) (C_2 × <u>)`, which is in `B_A` by Part 3. Map `W *_θ -> G_M` by
  `w -> w` and `t -> u s`. The relation holds:
  `(u s) c (u s)^(-1) = u θ(c) u^(-1) = θ(c)`, because `u` centralizes `C_2`.
  - Take a Britton-reduced word `w_0 t^(ε_1) w_1 ... t^(ε_n) w_n` of `W *_θ`, with
    `n >= 1`. Substitute `t = u s`. Between consecutive `u`-letters the `M`-segments
    are:
    - `s w_i` for signs `(+, +)`;
    - `s w_i s^(-1)` for `(+, -)`. This is a pinch only if `s w_i s^(-1) ∈ C_2`, that
      is `w_i ∈ C_1`, which is excluded.
    - `w_i` for `(-, +)`. This is a pinch only if `w_i ∈ C_2`, which is excluded.
    - `w_i s^(-1)` for `(-, -)`.
  - So the image is reduced with `n` letters `u^(±1)`, and it is not `1`. The map is
    injective.
- **⟹.** Take `M = W *_θ` and `s = t`. `∎`
