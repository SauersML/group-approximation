---
rg: 2
id: a2-group-embeds-in-rs-two-graph-geometric-proof
kind: route
title: Proof by sector geometry that every vertex-free type rotating Ã₂ group acts on its Robertson–Steger boundary by finitely many cylinder exchanges, with no C*-algebra, simplicity or irreducibility input
target: a2-group-embeds-in-full-group-of-its-rs-two-graph
requires:
  - robertson-steger-a2-boundary-algebras-are-rank-two-ck
artifacts:
  - research/artifacts/gq-bh-bh-groupoid-frontier.md
---

**Lane proof (bh-groupoid, 2026-09-18), not independently reviewed. No novelty claimed.**
It reuses the geometric claim inside the proof of Robertson–Steger Theorem `main2`. It
never uses the map `φ`, simplicity of `𝒜`, or (H2)/(H3). So it holds for exotic buildings
too, not only for `PGL_3(K)`. For `PGL_3(K)` lattices,
`rank-two-prefix-replacement-groups-contain-infinite-kazhdan` proves item 2 below through
`φ` and simplicity.

## Setting and sources

- `B` is a locally finite thick building of type Ã₂, with boundary `Ω` and base vertex
  `O` of type 0.
- `Γ` is a group of type rotating automorphisms of `B` acting freely on the vertices, with
  finitely many orbits.
- Notation is Robertson–Steger §7 (arXiv:1302.5593, TeX read at source for this proof):
  - the model tile `𝔱` and model parallelograms `𝔭_m`;
  - `𝔗`, `𝔓_m`, the tile maps `o(p)`, `t(p)`, `A = Γ\𝔗` and `W_m`;
  - the decorations `D` (tiles based at `O`), `δ: D -> A` (injective), and `W̄_m`;
  - `𝔚̄_m` (parallelograms `p` with `p(0,0) = O`), `ᾱ(p) = (o(p), α(Γp))`, and
    `Ω(p) = {ω : p(𝔭_m) ⊂ [O,ω)}`.
- Imported from the source:
  - **(RS1)** Lemma `oalpha`: `ᾱ: 𝔚̄_m -> W̄_m` is a bijection. It uses (H1) through
    Lemma `frWm`, and (H1) holds for every such `Γ`
    (`robertson-steger-a2-boundary-algebras-are-rank-two-ck`, item 1).
  - **(RS2)** Lemma `c1`: the sets `Ω(p)`, `p ∈ 𝔚̄_m`, partition `Ω`.
  - **(RS3)** Lemma `c2`: the `Ω(p)` form a basis of the topology of `Ω`.
  - **(RS4)** Lemma `c3`, in the form in which the proof of Corollary `9B` applies it,
    with the far corner fixed. Let `q ∈ 𝔓_m` with base `y = q(0,0)` and far corner
    `x = q(m+(1,1))`, and let `y'` have graph distance `n ≤ m_1, m_2` from `y`. Then
    `conv(x,y')` contains the sub-parallelogram of `q` of shape `m − (n,n)` at the corner
    `x`.
  - **(RS5)** Corollary `9B`: in the same situation, `conv(x,y')` is the image of a
    unique `q'' ∈ 𝔓` with `q''(0,0) = y'` and `t(q'') = t(q)`.
- Standard building facts, cited and not re-read:
  - **(B1)** For every vertex `v` and every `ω` there is a unique sector `[v,ω)` in the
    class `ω` based at `v` (Ronan, *Lectures on Buildings*, Thm 9.6, as cited by RS).
    Sectors lie in apartments and are convex.
  - **(B2)** Parallel sectors contain a common subsector (the definition of the classes
    in RS §7).
  - **(B3)** Automorphisms map sectors to sectors and classes to classes, and
    `g[v,ω) = [gv, gω)`.

For `ω ∈ Ω` write `s_ω: 𝔰 -> B` for the type rotating isometry of the model sector
`𝔰 = ⋃_m 𝔭_m` onto `[O,ω)`. It is unique, since the types of the vertices fix the
orientation. Its restriction to `𝔭_m` is the unique `p ∈ 𝔚̄_m` with `ω ∈ Ω(p)` (RS2).

## Step 1. The coding homeomorphism

- **The 2-graph.** Let `Λ = Λ_Γ` be the finite 2-graph with vertex set `A` and
  `Λ^m = W_m`. Factorization is unique by (H1). Every vertex emits edges of both colours,
  because every parallelogram lies in an apartment and extends there by one row or one
  column.
- **Its path space.** `Λ^∞` is the space of maps `x: Z²_+ -> A` whose restrictions to the
  boxes `[0,m]` lie in `W_m`, with the cylinder topology. Write
  `Z(w) = {x : x|[0,m] = w}` for `w ∈ W_m`, and `(σ^n x)(l) = x(n+l)`.
- **The clopen image.** Put `Y = ⊔_{d∈D} Z(δ(d))`. It is clopen because `δ` is injective.
- **The coding map.** Define `h: Ω -> Y` by `h(ω)(l) = Γ·(s_ω)_l`, where
  `(s_ω)_l ∈ 𝔗` is the tile `l' ↦ s_ω(l+l')`. Then `h(ω)|[0,m] = α(Γ s_ω|_{𝔭_m})` and
  `h(ω)(0) = δ(o(s_ω))`.

**Claim 1.** `h` is a homeomorphism, and `h(Ω(p)) = Z(α(Γp))` for `p ∈ 𝔚̄`. Since
`o(p) = δ^{-1}(α(Γp)(0))`, the decoration is recovered from the word.

- **Injective.** Suppose `h(ω) = h(ω')`. Both have the same decoration, so
  `ᾱ(s_ω|_{𝔭_m}) = ᾱ(s_ω'|_{𝔭_m})` for every `m`. By RS1, `s_ω = s_ω'`, and so
  `ω = ω'`.
- **Surjective.** Let `x ∈ Y`, and put `d = δ^{-1}(x(0))`.
  - By RS1, for each `m` there is a unique `p_m ∈ 𝔚̄_m` with `ᾱ(p_m) = (d, x|[0,m])`.
  - These are compatible: the restriction of `p_{m'}` to `𝔭_m` has the same `ᾱ`.
  - Each `Ω(p_m)` is nonempty, since `p_m(𝔭_m)` lies in an apartment and extends to a
    sector there.
  - Each `Ω(p_m)` is compact, being clopen by RS2 and RS3.
  - So `⋂_k Ω(p_{(k,k)})` contains some `ω`, and `h(ω) = x`.
- **Homeomorphism.** `h^{-1}(Z(α(Γp))) = Ω(p)` is open, so `h` is continuous. A continuous
  bijection from a compact space onto a Hausdorff space is a homeomorphism.

## Step 2. Each γ is a finite cylinder exchange

Fix `γ ∈ Γ`, and choose `m` with `n := d(O, γ^{-1}O) ≤ m_1, m_2`, as in `main2`. Put
`y' = γ^{-1}O`.

Fix `p ∈ 𝔚̄_m`. RS5, applied to `p` with far corner `p(m+(1,1))`, gives `p'' ∈ 𝔓_{m''}`
with `p''(0,0) = y'` and `t(p'') = t(p)`. Put `p' = γp'' ∈ 𝔚̄_{m''}`. These depend only on
`γ` and `p`.

**Claim 2.** For every `ω ∈ Ω(p)`:
- `[y',ω) ⊇ p''(𝔭_{m''})`;
- the subsector `S_t = s_ω(m+𝔰)` of `[O,ω)` is the subsector of `[y',ω)` at shape `m''`.

*Proof.*
1. By B2, `[y',ω)` and `[O,ω)` share a subsector. So the far corners
   `z_k = s_ω(m+(k+1,k+1))` lie in `[y',ω)` for all large `k`.
2. **S_t lies in [y',ω).** Let `v = s_ω(m+l)` be a vertex of `S_t`, and take
   `k ≥ l_1, l_2` large.
   - Apply RS4 to `q_k = s_ω|_{𝔭_{m+(k,k)}}`, whose base `O` has distance `n` from `y'`.
     Then `conv(z_k, y')` contains the part of `q_k` from coordinate `(n,n)` to its far
     corner, and this part contains `v` because `m ≥ (n,n)`.
   - `z_k` and `y'` lie in the convex set `[y',ω)`, so `v ∈ [y',ω)`.
   - Hence `S_t ⊆ [y',ω)`.
3. **The initial parallelogram.** In particular `p(m+(1,1)) ∈ [y',ω)`. So
   `conv(y', p(m+(1,1))) = p''(𝔭_{m''})` lies in `[y',ω)`.
   - It is a parallelogram based at the base vertex `y'` of the sector, with matching
     types.
   - So it is the initial parallelogram: `s'|_{𝔭_{m''}} = p''`, where `s'` parametrizes
     `[y',ω)`.
4. **The subsector.** `S_t ⊆ [y',ω)` is a sector based at `p(m)` with initial tile
   `t(p) = t(p'') = s'|_{m''+𝔱}`. Two type rotating isometries of `𝔰` into one apartment
   that agree on a tile are equal. So `S_t = s'(m''+𝔰)`. ∎

**Consequence.** By B3, `γ[y',ω) = [O, γω)`, so `s_{γω} = γ∘s'`.
- `s_{γω}|_{𝔭_{m''}} = γp'' = p'`.
- `Γ`-classes of tiles are `Γ`-invariant, so
  `h(γω)(m''+l) = Γ·s'_{m''+l} = Γ·(s_ω)_{m+l} = h(ω)(m+l)` for all `l`.
- Put `u = α(Γp)` (degree `m`) and `u' = α(Γp')` (degree `m''`). Then
  `t(u) = Γt(p) = Γt(p') = t(u')`, and
  `h γ h^{-1}(u z) = u' z` for every `z` with `z(0) = t(u)`.

So `h γ h^{-1}` maps each cylinder `Z(u)`, `p ∈ 𝔚̄_m`, onto `Z(u')` by prefix replacement.
- The `Z(u)` partition `Y` (RS2 and Claim 1).
- The `Z(u')` are the images `h(γΩ(p))`, so they partition `Y` too.
- Extend by the identity on `Λ^∞ \ Y = ⊔_{a ∉ δ(D)} Z(a)`.

This shows that `h γ h^{-1}` lies in the cylinder-exchange group `[[Λ_Γ]]` of
`brick-coded-two-graph-full-groups-embed-in-brin-thompson`. Its pieces `Z(u', u)` are
compact open bisections of the path groupoid of `Λ_Γ`, so it also lies in the
topological full group `[[G_{Λ_Γ}]]`.

## Step 3. Faithfulness

`γ ↦ hγh^{-1}` is a homomorphism, being conjugation of an action. It is injective iff
`Γ` acts faithfully on `Ω`.

Suppose `γ ≠ 1` acts trivially on `Ω`. The following steps use standard facts, cited and
not re-read (Abramenko–Brown, *Buildings*, §§11.8–11.9, on the building at infinity with
its complete apartment system):
1. **γ fixes every apartment.** Every apartment `𝒜` is the unique apartment whose
   boundary contains a given pair of opposite chambers at infinity of `𝒜`. So `γ𝒜 = 𝒜`.
2. **γ is a translation on 𝒜.** `γ|_𝒜` is an automorphism of the Ã₂ Coxeter complex that
   fixes all six boundary chambers of `𝒜`.
3. **The translation vector vanishes.**
   - The building at infinity is thick. So for each of the three wall directions there is
     an apartment `𝒜'` with `𝒜 ∩ 𝒜'` a half-plane bounded by a wall in that direction.
   - `γ` preserves `𝒜 ∩ 𝒜'` exactly, so the translation vector is parallel to that wall.
   - This holds for all three directions, so the vector is `0`.
4. **Contradiction.** So `γ` fixes a vertex, which contradicts freeness.

## Conclusion

`γ ↦ hγh^{-1}` is an injective homomorphism `Γ -> [[Λ_Γ]] ≤ [[G_{Λ_Γ}]]`. Each element
acts by finitely many cylinder exchanges `Z(u) -> Z(u')`, with shape offsets `m'' − m`.
This is the claim of `a2-group-embeds-in-full-group-of-its-rs-two-graph`.

It uses only (H1), the geometric lemmas of RS §7 and the standard building facts listed.
It does not use (H2), (H3), the map `φ`, simplicity, Kumjian–Pask's C*-identification or
Renault's reconstruction.
