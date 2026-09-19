---
rg: 2
id: bg-chains-are-residually-tf-solvable-so-g1n-targets-die-proof
kind: route
title: Killing the lower letters of a chain leaves a free product of conjugates of the fibre acted on by BS(1, n); its Cartesian subgroup is free, so the derived series of that free group cuts the chain down to 𝒮-groups
target: bg-chains-are-residually-tf-solvable-so-g1n-targets-die
requires:
  - commutator-root-frontier-kills-pl-and-bi-ordered-targets
---

## Inputs

- **(F5)** Item 5 of [[commutator-root-frontier-kills-pl-and-bi-ordered-targets]]: if `φ: G(K; α, β) → Q` and
  `φ(N)` lies in a subgroup of `Q` whose finitely generated subgroups are all residually 𝒮, then `φ(y) = 1`.
- **(BS)** Bass–Serre theory. A group acting on a tree with trivial edge stabilizers is the free product of
  the stabilizers of a set of orbit representatives of vertices, and of `π1` of the quotient graph. Kurosh: a
  subgroup of a free product that meets no conjugate of a factor is free.
- **(S)** 𝒮 is closed under subgroups (intersect the series) and finite direct products. A direct sum of
  `𝒮`-groups with series of bounded length is in 𝒮. `Z` and `BS(1, n) = Z[1/n] ⋊ Z` are in 𝒮, for `n ≠ 0`.
- A free group `F` has `F^{(k)}/F^{(k+1)}` free abelian and `∩_k F^{(k)} = 1`.

## Item 1: the amalgamation lemma

Let `Γ ∈ 𝒮` with normal series `Γ = Γ_0 ⊃ … ⊃ Γ_ℓ = 1`, let `z ∈ Γ` have infinite order, and let
`ρ: Γ → <z>` be a retraction with kernel `J`. Let `B ∈ 𝒮` and let `c ∈ B` have infinite order. Put
`Δ = Γ *_{z = c} B`.

**The retraction.** `ρ` followed by `z ↦ c`, together with the identity of `B`, agree on `<z> = <c>`. So they
define a retraction `π: Δ → B`. Let `L = ker π`.

**Structure of `L`.** `Δ` acts on its Bass–Serre tree `T`, which has vertices `Δ/Γ ⊔ Δ/B` and edges `Δ/<c>`.
- `L` is normal and meets every conjugate of `<c>` and of `B` trivially, since `π` is injective on `B`. So
  edge stabilizers in `L` are trivial.
- The stabilizer of the vertex `gΓ` in `L` is `L ∩ gΓg^{-1} = g J g^{-1}`.
- Orbits: `L\Δ/Γ ≅ B/π(Γ) = B/<c>`, `L\Δ/B` is one point and `L\Δ/<c> ≅ B/<c>`. The edge `b<c>` joins the
  vertex `b<c>` to the single `B`-vertex. So `L\T` is a star, which is a tree.
- By (BS), `L = *_{i ∈ B/<c>} J_i` with `J_i = b_i J b_i^{-1}`, where the `b_i ∈ B` are coset representatives.
- `B` permutes the factors. If `b b_i = b_{i'} c^e`, then `b J_i b^{-1} = b_{i'} (z^e J z^{-e}) b_{i'}^{-1} = J_{i'}`,
  and the identification `J → J_{i'}` is twisted by conjugation by `z^e ∈ Γ`.

**The series.** Put `J_j = J ∩ Γ_j`. These are normal in `Γ`, and `J_j/J_{j+1}` embeds in `Γ_j/Γ_{j+1}`. Let
`q: L → ⊕_i J_i` be the map that is the identity on each factor, and let `K = ker q`, the Cartesian subgroup.
Consider:

`Δ ⊃ π^{-1}(B_1) ⊃ … ⊃ π^{-1}(B_{ℓ'}) = L = L_0 ⊃ L_1 ⊃ … ⊃ L_ℓ = K ⊃ K' ⊃ K'' ⊃ … ⊃ K^{(k)}`,

where `B = B_0 ⊃ … ⊃ B_{ℓ'} = 1` is a normal series of `B` with torsion-free abelian factors, and
`L_j = q^{-1}(⊕_i J_{i,j})`, with `J_{i,j}` the copy of `J_j` in `J_i`.
- The terms `π^{-1}(B_j)` are normal in `Δ` with factors `B_j/B_{j+1}`.
- `L_j` is normal in `Δ`.
  - `L` acts on `⊕_i J_i` through `q` by inner automorphisms, which preserve `⊕_i J_{i,j}`.
  - `B` permutes the factors, twisting by `z^e`. Since `J_j ⊴ Γ`, this also preserves `⊕_i J_{i,j}`.
  - `Δ = L ⋊ B`, so `L_j` is normalized by all of `Δ`.
- `L_j / L_{j+1} ≅ ⊕_i J_j/J_{j+1}`, which is torsion-free abelian. And `L_ℓ = q^{-1}(1) = K`.
- `K` meets no conjugate of a factor `J_i`, because `q` is injective on each factor. By Kurosh, `K` is free.
- `K ⊴ Δ`, being the preimage of `⊕_i J_{i,ℓ} = 1`, so each `K^{(k)}`, characteristic in `K`, is normal in `Δ`.
  Its factors `K^{(k)}/K^{(k+1)}` are free abelian.

So `Δ/K^{(k)} ∈ 𝒮` for every `k`, and `∩_k K^{(k)} = 1`. Hence `Δ` is residually 𝒮. ∎

## Item 2: finite chains

Write `C_m = C_m(n)`. The relations of `C_{m+1}` are those of `C_m` together with `c_{m+1}^{-1} c_m c_{m+1} = c_m^n`.
So `C_{m+1} = C_m *_{<c_m>} B` with `B = <c_m, c_{m+1}> ≅ BS(1, n)`, in which `c_m` has infinite order.
Sending `c_0, …, c_{m-1}` to `1` respects every relation, so it gives a retraction `ρ_m: C_m → <c_m>`. Put
`J^{(m)} = ker ρ_m`.

**Induction claim.** There are normal subgroups `X_{m,1} ⊃ X_{m,2} ⊃ …` of `C_m`, contained in `J^{(m)}`, with
`∩_k X_{m,k} = 1` and `C_m/X_{m,k} ∈ 𝒮`.
- In particular `c_m` survives with infinite order in each `C_m/X_{m,k}`, and `ρ_m` descends to a retraction.

**Base.** `C_0 = <c_0> ≅ Z`. Take `X_{0,k} = 1`.

**Step.** Fix `k` and put `Γ = C_m / X_{m,k}`.
- `X_{m,k} ∩ <c_m> = 1`, because `X_{m,k} ⊂ J^{(m)}`. So the quotient of `C_{m+1}` by the normal closure of
  `X_{m,k}` is `Δ_k = Γ *_{<c_m>} B`.
- Item 1 applies to `Δ_k`, giving `K_k ⊴ Δ_k` with `Δ_k / K_k^{(j)} ∈ 𝒮`. Let `Y_{k,j} ⊴ C_{m+1}` be the preimage
  of `K_k^{(j)}`.
- `Y_{k,j}` lies in the preimage of `L = ker(Δ_k → B)`, which lies in `J^{(m+1)} = ker ρ_{m+1}`. This holds because
  `ρ_{m+1}` factors through `B → <c_{m+1}>`, which kills `c_m`.

**Trivial intersection.** Let `1 ≠ g ∈ C_{m+1}`.
- If `π(g) ≠ 1` in `B`, then `g ∉ Y_{k,j}` for all `k, j`, since every `Δ_k/K_k^{(j)}` maps onto `B` compatibly.
- Otherwise `g ∈ L_∞ = ker(C_{m+1} → B)`. By item 1 applied to `C_{m+1}` itself (the Bass–Serre part needs no
  𝒮 hypothesis), `L_∞ = *_i b_i J^{(m)} b_i^{-1}`.
  - Write `g` in reduced form. It has finitely many syllables `b_i s b_i^{-1}`, each with `1 ≠ s ∈ J^{(m)}`.
  - Choose `k` with no `s` in `X_{m,k}`. This is possible since the family is nested with trivial intersection.
  - The image of `L_∞` in `Δ_k` is `*_i b_i (J^{(m)}/X_{m,k}) b_i^{-1}`, and `g` maps to a reduced word with
    nontrivial syllables, so it survives in `Δ_k`.
  - Then `g ∉ Y_{k,j}` for `j` large, by item 1.

So the countable family `{Y_{k,j}}` has trivial intersection. Its finite intersections `X_{m+1,·}` are nested, lie
in `J^{(m+1)}`, and have quotients in 𝒮, since `C_{m+1}/(Y ∩ Y')` embeds in `C_{m+1}/Y × C_{m+1}/Y'`. Enumerate
them to get the chain `X_{m+1,1} ⊃ X_{m+1,2} ⊃ …`.

The same argument works when the edge exponents `n_i ≠ 0` vary with `i`. ∎

## Item 3: the kernel of `G(1, n)`

- Reidemeister–Schreier for `s`: `M = ker(G(1, n) → Z) = <c_i (i ∈ Z) | c_{i+1}^{-1} c_i c_{i+1} = c_i^n>`.
- The segment groups `C_{[a,b]}`, with the presentation of `C_{b-a}` on `c_a, …, c_b`, satisfy:
  - `C_{[a,b+1]} = C_{[a,b]} *_{<c_b>} BS(1, n)`;
  - `C_{[a-1,b]} = BS(1, n) *_{<c_a>} C_{[a,b]}`.

  Both amalgamated subgroups are infinite cyclic on both sides, so both inclusions are injective.
- So `M` is the directed union of copies of the `C_m`. A finitely generated subgroup of `M` lies in one of them,
  hence is residually 𝒮 by item 2. ∎

## Item 4: the kill

- `N^ab = (Z/K)[t^{±1}]` is torsion, so the `s`-exponent map, whose target `Z` is torsion-free, kills `φ(N)`.
  Hence `φ(N) ≤ M`.
- By item 3 and (F5), `φ(y) = 1`.

This is uniform in `n ≠ 0` and in the six groups, hence in the 26 words. ∎

## Checks

- Only `B = BS(1, n) ∈ 𝒮` and the infinite order of `c_m` in it are used. So every `n ≠ 0` is covered,
  including `n = 1`, where `BS(1, 1) = Z^2`.
- `n = -1`: `BS(1, -1)` is the Klein bottle group, `Z ⋊ Z ∈ 𝒮`. Item 1 does not need `B` to be bi-orderable.
- Consistency: w13's bounded search found no map for `n = 2, -1, -2` (`bg2-4.out`), as item 4 predicts.
