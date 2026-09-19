---
rg: 2
id: heisenberg-in-mv-reduces-to-zn-subshift-realization-proof
kind: route
title: Relator cocycles of the Assouad configuration vanish on a dense orbit hence everywhere, so they lift along any equivariant map from commuting mV elements; product hosts are read off at one free point
target: heisenberg-in-mv-reduces-to-zn-subshift-realization
requires:
  - heisenberg-group-embeds-in-wobbling-group-of-some-zn
  - faithful-heisenberg-actions-are-locally-free-at-every-scale
---

Notation as in the claim. `F(S)` is the free group on `a, b`. A word is read right to left, so
`s_1` is applied first. For `w ∈ F(S)`, `ŵ` is the image of its class in `H` under `h ↦ ĥ`. This is
a homomorphism, since `R_{gh} = R_g R_h`, and so `ŵ = ŝ_k ∘ ⋯ ∘ ŝ_1`.

## Step 1: cocycles along the base orbit

Claim: `c_w(σ^z x_ι) = ŵ(z) − z` for all `z ∈ Z^N` and all words `w`.

The proof is by induction on `|w|`. The empty word is clear. For `s w'`, put `ξ = σ^z x_ι` and
`c = c_{w'}(ξ) = ŵ'(z) − z`. Then `σ^c ξ = σ^{ŵ'(z)} x_ι`, so

`d_s(σ^c ξ) = x_ι(ŵ'(z))_s = ŝ(ŵ'(z)) − ŵ'(z)`.

Adding `c` gives `ŝŵ'(z) − z`.

The value `c_w(ξ)` is computed from `ξ` alone, so the formula is consistent even if
`σ^z x_ι = σ^{z'} x_ι` for some `z ≠ z'`.

## Step 2: part (A)

`d_s` depends on `ξ(0)` only. By induction, `c_w` depends only on `ξ|_{B_{K|w|}}`, so it is locally
constant.
- If `w = 1` in `H`, then `ŵ = id`, and Step 1 gives `c_w = 0` on the dense set `{σ^z x_ι}`. So
  `c_w ≡ 0` on `X_ι`.
- If `w ≠ 1` in `H`, then `c_w(x_ι) = ŵ(0) = ι(1·w^{-1}) ≠ ι(1) = 0`, since `ι` is injective.

## Step 3: the general lift, part (B)

Let `X ⊆ A^{Z^N}` be shift-invariant, and suppose `c_w ≡ 0` on `X` for every relator `w`,
including `s^{-1}s`. Take `h_i`, `U`, `π` as in (B).
- **Equivariance for all vectors.** `π(h^v u) = σ^v π(u)` for all `v ∈ Z^N`, since the `h_i`
  commute.
- **Words.** Put `L_s(u) = h^{d_s(π u)} u`. By induction, `L_w(u) = h^{c_w(π u)} u` for `u ∈ U`.
  With `v = c_{w'}(π u)`,

  `L_s(L_{w'} u) = h^{d_s(π(h^v u))} h^v u = h^{d_s(σ^v π u) + v} u = h^{c_{s w'}(π u)} u`.

  Each `L_s` maps `U` into `U`, because `U` is invariant.
- **Homeomorphisms.** `L_{s^{-1}} L_s = L_{s^{-1}s} = h^0 = id` on `U`. So each `L_s` is a
  bijection of `U`.
  - It is continuous, because `d_s ∘ π` is locally constant.
  - Extended by the identity off `U`, it lies in `mV`. This is the argument of
    `brin-thompson-groups-contain-full-groups-of-their-elements`: `d_s ∘ π` takes finitely many
    values `v_j` on clopen sets `U_j`. Each `h^{v_j}` is in `mV`. Intersecting its domain boxes
    with a box decomposition of `U_j` gives prefix replacements on boxes.
- **Homomorphism.** `w ↦ L_w` is a homomorphism `F(S) → mV` that kills every relator, so it factors
  through `H`.
- **Injective.** Let `w ≠ 1` in `H`. Then `L_w(u_0) = h^{c_w(π u_0)} u_0 ≠ u_0`, because the
  stabilizer of `u_0` is trivial and `c_w(π u_0) ≠ 0`.

For `X = X_ι` and `π(u_0) = x_ι`, the condition `c_w(x_ι) ≠ 0` is Step 2. This proves (B). ∎

## Step 4: part (C), 1 ⇒ 2

Let `ρ : H → [[Z^N ↷ Y]]` be injective. For `y ∈ Y`, write `T^v y = (T_1^{v_1} y_1, …)`.
- **The action is free.** `T^v y = y` forces `T_i^{v_i} y_i = y_i` for each `i`, so `v = 0` by
  aperiodicity. So each `g ∈ [[Z^N ↷ Y]]` has a unique continuous cocycle `m_g`, with
  `g(y) = T^{m_g(y)} y`, and `Fix(g) = {m_g = 0}` is clopen.
- **Product dependence.** `m_s` is locally constant on the compact product `Y`. So it is constant on
  the pieces of a finite partition into clopen rectangles.
  - Refine to product partitions `P_i` of `Y_i`. Then
    `m_s(y) = F_s(P_1(y_1), …, P_N(y_N))`, where `P_i(y_i)` is the cell containing `y_i`.
  - Put `W_i = P_i` and `F_s := m_s` on cells.
- **A point with trivial stabilizer.** `ρ` is faithful, so by
  `faithful-heisenberg-actions-are-locally-free-at-every-scale` each
  `K_R = Y ∖ ⋃_{1 ≠ g ∈ B_w(R)} Fix(ρ g)` is nonempty.
  - Each `K_R` is closed, because each `Fix(ρ g)` is clopen.
  - The `K_R` decrease in `R`.
  - By compactness there is `y ∈ ⋂_R K_R`, with trivial `H`-stabilizer.
- **Reading off the realization.** Put `κ_i(t) = P_i(T_i^t y_i)`. The orbit map `z ↦ T^z y` is a
  bijection of `Z^N` onto the `Z^N`-orbit of `y`, which is `ρ(H)`-invariant.
  - `ρ(s)(T^z y) = T^{z + m_s(T^z y)} y = T^{π_s(z)} y`, so `ρ(s)` restricted to the orbit is
    `π_s`.
  - Hence the `π_s` are bijections defining an `H`-action. The orbit of `0 ↔ y` is free.

## Step 5: part (C), 2 ⇒ 1, and the mV consequence

- **The systems.** Fix a Sturmian sequence `β ∈ {0,1}^Z`. Let `Y_i` be the orbit closure of
  `κ_i' = (κ_i, β)` in `(W_i × {0,1})^Z`. It is aperiodic, since its second coordinate lies in the
  aperiodic Sturmian subshift. Put `y* = (κ_1', …, κ_N') ∈ Y`, and
  `m_s(y) = F_s(y_1(0)^{(1)}, …, y_N(0)^{(1)})`, where the superscript `(1)` picks the `W_i`-part.
- **Relators.** As in Step 2, `c_w(y)` depends only on the radius-`K|w|` windows of the `y_i`.
  - Each window of `y_i ∈ Y_i` occurs in `κ_i'` at some `t_i`. The coordinates are independent, so
    the tuple of windows of `y` occurs at `t = (t_1, …, t_N)` in `y*`.
  - Hence `c_w(y) = c_w(T^t y*) = π_w(t) − t`, which is `0` for a relator `w`, by the Step 1
    computation with `π` in place of `ŵ`.
- **Homeomorphisms and faithfulness.** So `ρ(s)(y) = T^{m_s(y)} y` are homeomorphisms defining an
  `H`-action by elements of `[[Z^N ↷ Y]]`. The action is faithful: on the free `Z^N`-orbit of `y*`
  it is the `π`-action, which has a free orbit.
- **Into `mV`.** Suppose `g_i ∈ m_iV` preserves a clopen `U_i`, and `π_i : U_i → Y_i` is a factor
  map. Let `h_i` act as `g_i` on the `i`-th block of coordinates of `C^{m_1 + ⋯ + m_N}`, and as the
  identity on the others.
  - The `h_i` commute and lie in `(Σ m_j)V`, and `π = ∏ π_i` is equivariant on `U = ∏ U_i`.
  - `Z^N` acts freely on `U`, since an extension of a free action is free.
  - Take `u_0 ∈ π^{-1}(y*)`. Then `c_w(y*) = π_w(0) ≠ 0` for `w ≠ 1`, because the orbit of `0` is
    free.
  - Step 3, with `X = Y` and `d_s = m_s`, gives `H ≤ (Σ m_j)V`. ∎
