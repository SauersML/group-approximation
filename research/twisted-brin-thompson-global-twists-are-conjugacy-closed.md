---
rg: 2
id: twisted-brin-thompson-global-twists-are-conjugacy-closed
kind: claim
title: In a twisted Brin--Thompson group the global twists are conjugacy-closed, so SV_G adds no conjugacies to its actor, and an HNN input whose base sits in the global twists needs a base-faithful image of itself inside the actor
requires:
  - twisted-bt-quasi-retract-onto-acting-group-citation
distinct_from:
  twisted-bt-quasi-retract-onto-acting-group-citation: that imports the coarse retraction h -> gtwist_κ(h); this evaluates the same cocycle at a constant point, where it is exact on every conjugation between global twists.
  baumslag-gersten-group-satisfies-boone-higman: its 2026-09-18 Attempts entry records the BG instance; this is the general statement for all subgroups and all HNN inputs.
  type-a-actors-have-no-proper-power-cyclic-edge-splittings: that forbids proper-power edge conjugacies in the actor itself; this shows the twisted host cannot supply them between global twists either.
---

**ESTABLISHED** (lane proof, elementary; not reviewed; no priority claimed).

## Setting

Let `G ≤ Sym(S)` act faithfully, and let `SV_G` be the twisted Brin--Thompson group of Belk--Zaremsky,
arXiv:2001.04579. The following was read at source (TeX on MSI):
- `τ_g` is the twist homeomorphism `τ_g(κ)(s) = κ(g^-1 s)` (l.273–277), and `ι(g) = τ_g` is an embedding
  `G → SV_G`.
- For `h ∈ SV_G` and `κ ∈ C^S`, the germinal twist `gtwist_κ(h) ∈ G` is defined at l.318.
- It is multiplicative (l.322–324): `gtwist_κ(h_2 h_1) = gtwist_{h_1 κ}(h_2) gtwist_κ(h_1)`.
- Clearly `gtwist_κ(τ_g) = g` for every `κ`.

Call `κ` **constant** if `κ(s)` is the same point of `C` for all `s ∈ S`. Every `τ_g` fixes every
constant point.

## Statement

Fix a constant point `κ`.
1. **Transporter.** If `f ∈ SV_G` and `f τ_a f^-1 = τ_b` with `a, b ∈ G`, then `b = λ a λ^-1`, where
   `λ = gtwist_κ(f)`.
2. **Transporter set.** For every `A ≤ G`,
   `{f ∈ SV_G : f ι(A) f^-1 ⊆ ι(G)} = ι(G) · C_{SV_G}(ι(A))`.
3. **Intersections are centralizers.** For every `u ∈ SV_G`, put `μ = gtwist_κ(u)` and `w = τ_μ^-1 u`.
   Then `ι(G) ∩ u^-1 ι(G) u = ι(C_G(w))`, where `C_G(w) = {a ∈ G : τ_a w = w τ_a}`.
4. **No new conjugacies.** Two elements `a, b ∈ G` are conjugate in `SV_G` iff they are conjugate in `G`.
   Likewise, if `f ι(A) f^-1 = ι(B)` for subgroups `A, B ≤ G`, then `B = λ A λ^-1`.
5. **HNN inputs.** Let `H = ⟨K, t | t c t^-1 = θ(c), c ∈ C⟩` be an HNN extension of `K` along
   `θ : C → K`. Let `Φ : H → SV_G` be a homomorphism with `Φ(K) ⊆ ι(G)`. Put `j = ι^-1 ∘ Φ|_K` and
   `λ = gtwist_κ(Φ(t))`. Then `k ↦ j(k)`, `t ↦ λ` defines a homomorphism `H → G`. If `Φ` is injective on
   `K`, the image is a quotient of `H` into which `K` embeds.
6. **Local form.** For every `κ' ∈ C^S`, `gtwist_κ'` restricts to a homomorphism
   `Stab_{SV_G}(κ') → G`.

## Proof

1. Take germinal twists at `κ` on both sides of `f τ_a = τ_b f`. Since `τ_a κ = κ`, the left side gives
   `gtwist_κ(f) · a = λ a`. The right side gives `gtwist_{fκ}(τ_b) · gtwist_κ(f) = b λ`. So `λ a = b λ`.
2. `⊇` is clear. For `⊆`, by 1 the element `τ_λ^-1 f` conjugates each `τ_a` to
   `τ_λ^-1 τ_{λ a λ^-1} τ_λ = τ_a`.
3. Suppose `u τ_a u^-1 ∈ ι(G)`. By 1 it equals `τ_μ τ_a τ_μ^-1`, so `w` commutes with `τ_a`. Conversely,
   if `w` commutes with `τ_a`, then `u τ_a u^-1 = τ_μ τ_a τ_μ^-1 ∈ ι(G)`.
4. Use 1, and `f = τ_c` for the converse.
5. `j` is a homomorphism on `K`. For `c ∈ C`, `Φ(t) τ_{j(c)} Φ(t)^-1 = τ_{j(θ(c))}`, so by 1,
   `j(θ(c)) = λ j(c) λ^-1`. The defining relations of `H` therefore hold for `j` and `λ` in `G`.
6. If `h_1 κ' = κ'`, multiplicativity reads `gtwist_κ'(h_2 h_1) = gtwist_κ'(h_2) gtwist_κ'(h_1)`. ∎

## Instances

- **Baumslag--Solitar.** If `BS(m,n) = ⟨a, t | t a^m t^-1 = a^n⟩` embeds with `a ↦ τ_α`, then `G` contains
  `α` of infinite order and `λ` with `λ α^m λ^-1 = α^n`.
- **Baumslag--Gersten** (`baumslag-gersten-group-satisfies-boone-higman`, Attempts, 2026-09-18). With
  `K = ⟨a, b⟩ ≅ BS(1,2)` placed globally, `G` must contain a quotient of `BG` in which `BS(1,2)` survives,
  for example `H_n ⋊ C_n` with `n ≥ 4` (`baumslag-gersten-group-maps-onto-higman-groups`).
- **Mapping tori.** Let `K ⋊_θ Z` be the mapping torus of an automorphism `θ` of `K`. If `K` is placed
  globally, then `θ` becomes conjugation by `λ` on `j(K) ≤ G`.

## Lesson for general BH

The twisted Brin--Thompson construction is conjugacy-rigid on its actor. At a constant point, the
germinal twist turns every conjugation between global twists into a conjugation inside `G`. So `SV_G`
repairs no missing conjugacy of `G`, such as a proper-power edge or an automorphism that is not inner. An
HNN or mapping-torus input can use `SV_G` beyond `G` only if its edge groups are placed with
non-constant twist cocycles, that is, on proper bricks. Even there, item 6 forces the local twists at
common fixed points to satisfy the same relations inside `G`. A design that puts an input's base inside
`ι(G)` needs a base-faithful quotient of the input to be inside `G` already, and `SV_G` adds nothing to
that quotient's conjugacy structure.
