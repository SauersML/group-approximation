---
rg: 2
id: rs-boundary-groupoid-is-expansive-amenable-kazhdan-host-proof
kind: route
title: "Proof: every generator s_{v̄,ū} acts as a prefix replacement; the first shape at which two boundary points separate gives a group element that moves them into two fixed disjoint cylinders (expansivity); simplicity gives minimality; nuclearity gives amenability; products with G_2 by the product theorem"
target: rs-boundary-groupoid-is-expansive-amenable-kazhdan-host
requires:
  - rank-two-prefix-replacement-groups-contain-infinite-kazhdan
  - robertson-steger-boundary-cylinders-and-pure-infiniteness
  - robertson-steger-word-products-and-boundary-topology
  - discrete-kazhdan-groups-are-finitely-generated
  - nekrashevych-expansive-groupoid-criteria
  - ad-nuclear-crossed-product-gives-amenable-action
  - ample-groupoid-products-expansive-iff-factors-are
---

## References and conventions

**Abbreviations.**
- [RS-C] is `robertson-steger-boundary-cylinders-and-pure-infiniteness`:
  - (rel1), `f2`, Lemma `5`, φ, `c1`, `c2`, main2 and the Remark.
- [RS-W] is `robertson-steger-word-products-and-boundary-topology`:
  - finite alphabet, restrictions, (H1), Corollary 4 with `ūv = (d,uv)`, `D` finite, the
    boundary topology.
- [K2] is `rank-two-prefix-replacement-groups-contain-infinite-kazhdan`, items 1-4.
- [N] is `nekrashevych-expansive-groupoid-criteria`.
- [AD] is `ad-nuclear-crossed-product-gives-amenable-action`.
- [P] is `ample-groupoid-products-expansive-iff-factors-are`.

**Crossed product facts.** These are the textbook facts already used in
`rank-two-prefix-replacement-kazhdan-proof`:
- the faithful conditional expectation `E(f u_γ) = δ_{γ,1} f`;
- `C(Ω) ⊆ C(Ω)⋊Γ`;
- `u_γ f u_γ^* = f∘γ^{-1}`, hence `u_γ 1_U = 1_{γU} u_γ`;
- full = reduced (Remark).

Two clopen sets are equal iff their indicators are.

**Cells.** For `ū ∈ W̄` put `Ω[ū] = Ω(ᾱ^{-1}(ū))`. By Lemma `oalpha` (in [RS-C]'s
setting), `ᾱ: 𝔚̄_m → W̄_m` is a bijection, so the level-`m` cells are indexed by `W̄_m`,
a finite set by [RS-W]. By main2 in [RS-C], `φ(s_{ū,ū}) = 1_{Ω[ū]}`.

**Group elements of generators.** For `ū, v̄ ∈ W̄` with `t(ū) = t(v̄)`, let
`g(v̄,ū) ∈ Γ` be the element `γ` of the formula for φ, so that
`φ(s_{v̄,ū}) = u_{g(v̄,ū)} 1_{Ω[ū]} = 1_{Ω[v̄]} u_{g(v̄,ū)}`.

## Lemma A (cells and prefix replacements)

Let `ū = (d,u) ∈ W̄_m` and `v̄ ∈ W̄` with `t(v̄) = t(ū)`, and let `g = g(v̄,ū)`.

**(a)** `gΩ[ū] = Ω[v̄]`.

`1_{gΩ[ū]} u_g = u_g 1_{Ω[ū]} = 1_{Ω[v̄]} u_g`. Multiply on the right by `u_g^*`.

**(b)** For each `m`, the cells `Ω[x̄]`, `x̄ ∈ W̄_m`, partition `Ω`.

By `c1`, `Σ_{x̄∈W̄_m} 1_{Ω[x̄]} = 1` in `C(Ω)`. This is a pointwise identity of
indicator functions, so every point lies in exactly one cell.

**(c)** For `n ∈ Z²_+`, `Ω[ū] = ⊔ Ω[ūw]` over `w ∈ W_n` with `o(w) = t(ū)`.

Apply φ to `f2` with `u = v = ū`: `1_{Ω[ū]} = Σ_w 1_{Ω[ūw]}`, again pointwise.

**(d) Prefix replacement.** `gΩ[ūw] = Ω[v̄w]` for every `w ∈ W_n` with `o(w) = t(ū)`.

*(d1)* `s_{v̄,ū}s_{ūw,ūw} = s_{v̄w,ūw}`.
- By `f2`, `s_{v̄,ū} = Σ_{w'} s_{v̄w',ūw'}`, summed over `w' ∈ W_n` with `o(w') = t(ū)`.
- By (rel1b), each term times `s_{ūw,ūw}` equals `s_{v̄w',ūw'}s_{ūw',ūw'}s_{ūw,ūw}`.
- By Corollary 4, `ūw' = (d, uw')`, and `(uw')|_{[m,m+n]} = w'` by (H1). So `ūw' ≠ ūw`
  for `w' ≠ w`, both of shape `m+n`, and Lemma `5` kills those terms.
- The term `w' = w` is `s_{v̄w,ūw}`.

*(d2)* `s_{v̄w,ūw}s_{ū,v̄} = s_{v̄w,v̄w}`.
- By (rel1a) and (d1), `s_{ūw,ūw}s_{ū,v̄} = (s_{v̄,ū}s_{ūw,ūw})^* = s_{ūw,v̄w}`.
- So `s_{v̄w,ūw}s_{ū,v̄} = s_{v̄w,ūw}s_{ūw,ūw}s_{ū,v̄} = s_{v̄w,ūw}s_{ūw,v̄w} = s_{v̄w,v̄w}`.

*(d3)* Hence `s_{v̄,ū}s_{ūw,ūw}s_{ū,v̄} = s_{v̄w,v̄w}`. Apply φ, with
`φ(s_{ū,v̄}) = φ(s_{v̄,ū})^* = 1_{Ω[ū]}u_g^*`, and use `Ω[ūw] ⊆ Ω[ū]` from (c):
`u_g 1_{Ω[ūw]} u_g^* = 1_{Ω[v̄w]}`, that is, `1_{gΩ[ūw]} = 1_{Ω[v̄w]}`.

**(e) Last-row decomposition.** If `m_j ≥ 1`, let `ū' = (d, u|_{[0,m-e_j]}) ∈ W̄_{m-e_j}`
and `w = u|_{[m-e_j,m]} ∈ W_{e_j}` (undecorated restriction). Then `t(ū') = o(w)` and
`ū = ū'w`.
- By Corollary 4, `ū'w = (d, (u|_{[0,m-e_j]})w)`.
- By uniqueness in (H1), `(u|_{[0,m-e_j]})w = u`, since `u` has both restrictions.

## Step 1. Γ is infinite, finitely generated and Kazhdan; Ω is Cantor (up to perfectness)

- [K2] item 1: `Γ` is infinite with (T). By `discrete-kazhdan-groups-are-finitely-generated`,
  `Γ` is finitely generated.
- [RS-W] item 8: `Ω` is compact, Hausdorff and totally disconnected.
- By `c2`, the cells form a basis. There are countably many (each `W̄_m` is finite), so `Ω`
  is second countable and hence metrizable (Urysohn).
- `Ω ≠ ∅`: [K2] item 3 says the infinite group `Γ` acts faithfully on `Ω`, which is
  impossible on the empty set.

Perfectness is proved in Step 3. By Brouwer's characterization, `Ω` is then a Cantor set.

## Step 2. The action is expansive

**The finite obstruction set.**
- Let `A_0 = {t(x̄) : x̄ ∈ W̄} ⊆ A`, and fix `r_a ∈ W̄` with `t(r_a) = a` for each
  `a ∈ A_0`.
- Let `C` be the union of the clopen rectangles:
  - `Ω[x̄] × Ω[x̄']` for `x̄ ≠ x̄'` in `W̄_0`;
  - `Ω[r_a w] × Ω[r_a w']` for `a ∈ A_0`, `j ∈ {1,2}` and `w ≠ w'` in `W_{e_j}` with
    `o(w) = o(w') = a`.
- These are finitely many, since `W̄_0 ≅ D` and `A` are finite and `W_{e_j} ⊆ A^{[0,e_j]}`.
- Each rectangle misses the diagonal, by (b) and (c). So `W = Ω×Ω \ C` is an open
  neighbourhood of the diagonal.

**Claim.** If `x ≠ y`, some `h ∈ Γ` has `(hx, hy) ∈ C`.

- By `c2` and Hausdorffness, some cell `Ω[x̄]`, `x̄ ∈ W̄_m`, contains `x` and not `y`. By (b)
  the level-`m` cells of `x` and `y` differ.
- Choose such an `m` with `m_1 + m_2` minimal. Let `ū ≠ v̄` in `W̄_m` index the cells of
  `x` and `y`.

*Case `m = 0`.* Then `(x,y) ∈ Ω[ū] × Ω[v̄] ⊆ C`. Take `h = 1`.

*Case `m ≠ 0`.* Pick `j` with `m_j ≥ 1`.
- By (e), `ū = ū'w` and `v̄ = v̄'w'` with `ū', v̄' ∈ W̄_{m-e_j}` and `w, w' ∈ W_{e_j}`.
- By (c), `x ∈ Ω[ū']` and `y ∈ Ω[v̄']`. By minimality of `m` and (b), `ū' = v̄'`, so
  `w ≠ w'`.
- Let `a = t(ū') ∈ A_0` and `h = g(r_a, ū')`. By (d), `hx ∈ hΩ[ū'w] = Ω[r_a w]` and
  `hy ∈ Ω[r_a w']`. So `(hx,hy) ∈ C`.

**Consequences.**
- So `Γ ↷ Ω` is expansive in the sense of Proposition pr:expansivegroups (3) ([N] item 6).
- `Γ` is finitely generated and `Ω` is a Cantor set (Steps 1 and 3), so that proposition
  gives (1), (2) and (4). The groupoid `R = Γ × Ω` and the groupoid of germs are
  expansive, and the action is a subshift.
- Expansive includes compactly generated (reading in [N]). For `R` this is also direct:
  `E × Ω` generates for a finite symmetric generating set `E` of `Γ`.

## Step 3. Minimality, perfectness, infinite orbits

**Minimality.** Suppose `Y ⊊ Ω` is a nonempty closed invariant set.
- Restriction `C(Ω) → C(Y)` is `Γ`-equivariant and surjective. It induces a
  *-homomorphism `π: C(Ω)⋊Γ → C(Y)⋊Γ`, which is nonzero because `π(1) = 1_Y ≠ 0`.
- `Ω \ Y` is open and nonempty, so it contains a nonempty clopen cell `U` (`c2`).
- `1_U ≠ 0` in `C(Ω)⋊Γ`, and `π(1_U) = 0`.
- So `ker π` is a proper nonzero closed ideal, which contradicts simplicity (Remark).

**Perfectness.** If `{ω}` were open, every orbit, being dense, would meet it. Then
`Ω = Γω`, which is discrete and compact, hence finite. That contradicts [K2] item 4
(every orbit is infinite).

**Infinite orbits and no invariant measure.** This is [K2] item 4.

## Step 4. Amenability

- By the Remark, `C(Ω)⋊Γ` is simple, nuclear and purely infinite, and isomorphic to
  `C(Ω)⋊_rΓ`. So `C_r^*(Ω⋊Γ)` is nuclear.
- `Γ` is discrete. By [AD] Theorem 3.4, (4) ⇒ (1), the action is amenable (Definition
  2.1).

## Step 5. Full groups

**The action groupoid.**
- `F_g = {g} × Ω` is a compact open bisection with `s(F_g) = Ω` and `r(F_g) = gΩ = Ω`.
- `F_gF_h = {(g, hx)(h, x)} = {(gh, x)} = F_{gh}`, and `g ↦ F_g` is injective.

**The germ groupoid.** Take the groupoid of germs `[g, x]` of the action, as in [N]
item 6.
- The germs of `g` form a full bisection. The resulting map `Γ → [[germs]]` is a
  homomorphism, injective because the action is faithful ([K2] item 3).
- It is effective. A germ in the interior of the isotropy has a neighbourhood
  `{[g,y] : y ∈ U}` of isotropy germs. So `g` fixes the open set `U` pointwise, and
  `[g,x]` is the germ of the identity.
- Its orbits are the `Γ`-orbits, so it is minimal, and invariant probability measures
  are `Γ`-invariant measures, of which there are none.

## Step 6. The product with G_2

- [P] item 4 applies: `Γ` is finitely generated, `Ω` is a Cantor set, and `Γ ↷ Ω` is a
  subshift. So `R × G_2` is compactly generated and expansive.
- **Minimal.** The orbit of `(x,z)` is `Γx × G_2z`. Composability is coordinatewise, so
  every pair `(g,h)` with `s(g) = x`, `s(h) = z` is an element. `Γx` is dense (Step 3).
  `G_2z ∋ μz` for every word `μ`, via `(μz, |μ|, z)`, so it meets every cylinder.
- **Full group.** `g ↦ F_g × G_2^{(0)}` is an injective homomorphism into `[[R × G_2]]`,
  by the coordinatewise product.

This proves items 1-7 of the target.
