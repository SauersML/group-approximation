---
rg: 2
id: h4-case1-pure-normal-form-and-fibred-obstruction-proof
kind: route
title: Proof of the single-edge H_4 normal form, the blindness of A_x ∪ A_y, and the fibred 19-wall augmentation
target: h4-case1-pure-normal-form-and-fibred-obstruction
requires: []
---

Notation is as in the target claim. `V = ℂ^4` carries the complexified reflection arrangement `𝒜` of `H_4`
(60 walls). For a subset `ℬ ⊆ 𝒜`, `M(ℬ)` is its complement. `ℓ_x` and `ℓ_y` are the fixed lines of `W_X` and
`W_Y`. `𝒜_x` is the set of walls containing `ℓ_x`; `𝒜_y` and `𝒜_z` are defined in the same way.

**Inputs from the literature.**
- (L1) Van der Lek: for `T ⊆ S`, a small ball `U_T` around a generic point of the fixed flat of `W_T`
  satisfies `U_T ∩ M(𝒜) = U_T ∩ M(𝒜_T) ≃ M(𝒜_T)`. This identifies `P_T` with a subgroup of `P`. The inclusion
  `M(𝒜) ⊂ M(𝒜_T)` induces a retraction `ρ_T : P → P_T`.
- (L2) Compatibility of retractions (Godelle–Paris, via the Salvetti complex; the coset-projection formula).
  For `S, T` we have `ρ_T(P_S) ⊆ P_{S∩T}`, and `ρ_T|_{P_S} = ρ^S_{S∩T}`. For a `w ∈ W_S`, the `W_T`-component
  of `w` lies in `W_{S∩T}`.
- (L3) Fibre-type arrangements (Falk–Randell; Terao). Let `ℓ` be a modular flat of corank one in `L(ℬ)`. Then
  the linear projection `p : M(ℬ) → M(ℬ_ℓ)/ℓ` is a locally trivial fibration with fibre `ℂ` minus `k` points,
  where `k = |ℬ∖ℬ_ℓ|`. It has a section "at infinity", given by the local complement near `ℓ` as in (L1). So
  `π_1M(ℬ) = F_k ⋊ π_1M(ℬ_ℓ)`, and the action is the Artin action of the braid monodromy
  `μ : π_1M(ℬ_ℓ) → P_k`.
  The modularity test used below is standard. For any two walls `H, H' ∉ ℬ_ℓ`, the collision locus
  `p(H ∩ H')` must be a wall of `ℬ_ℓ`. With normals `a, b`, that locus has normal `(b·ℓ)a − (a·ℓ)b`.
- (L4) Artin: `P_k` acts faithfully on `F_k = ⟨x_1,…,x_k⟩` and fixes the boundary word `x_1⋯x_k`. This action,
  together with the Birman exact sequence `1 → F_{k-1} → P_k → P_{k-1} → 1`, is standard.

## (A) Normal form

*Step 1: pure double cosets.* We have `A_Y A_X ∩ P = P_Y P_X`. Indeed, suppose `ba^{-1} ∈ P` with `b ∈ A_Y` and
`a ∈ A_X`. Then `b̄ = ā ∈ W_X ∩ W_Y = W_Z`. Lift it to `l ∈ A_Z`. Then `bl^{-1} ∈ P_Y` and `la^{-1} ∈ P_X`.

*Step 2: the two splittings.* By (L2), `ρ_X|_{P_Y} = ρ^Y_Z` and `ρ_Y|_{P_X} = ρ^X_Z`, so both are retractions
onto `P_Z`. Hence `P_Y = F ⋊ P_Z` and `P_X = N ⋊ P_Z`. Also `F ∩ P_X = 1`, because `ρ_X` is the identity on
`P_X` and kills `F`. Likewise `N ∩ P_Y = 1`. Since `P_Z ⊆ P_X ∩ P_Y`:
- `P_YP_X = F·P_X`, with the `F`-factor unique;
- `P_XP_Y = N·P_Y`, with the `N`-factor unique.

`F ≅ F_3` is the fibre group of the `A_3 → A_2` Fadell–Neuwirth fibration, by (L3) applied to `𝒜_y ⊇ 𝒜_z`.

*Step 3: single-edge vertices are pure translates.* `π(gA_X) = x̄` iff `ḡ ∈ W_X` iff `g ∈ PA_X`. So each `x_i`
equals `p_iA_X` with `p_i ∈ P`, well defined modulo `P_X`. Similarly `y_i = q_iA_Y` with `q_i ∈ P`, modulo
`P_Y`. Two such vertices `pA_X` and `qA_Y` are adjacent iff `pA_X ∩ qA_Y ≠ ∅`. That holds iff
`q^{-1}p ∈ A_YA_X ∩ P = P_YP_X`, by Step 1.

*Step 4: walking around the hexagon.* Translate by `A` so that `x_1 = A_X` and `y_1 = A_Y`. We apply Steps 2
and 3 at each vertex in turn, and each time we pick the unique representative in `F` or `N`:
- `y_1 = A_Y` and `x_2` is adjacent to `y_1`, so `x_2 = α_1A_X` with a unique `α_1 ∈ F`.
- `x_2` and `y_2` are adjacent, so `y_2 = α_1β_1A_Y` with a unique `β_1 ∈ N`.
- In the same way, `x_3 = α_1β_1α_2A_X` and `y_3 = α_1β_1α_2β_2A_Y`.
- The edge `y_3x_1` gives `α_3 ∈ F` with `g := α_1β_1α_2β_2α_3 ∈ P_X`.

Uniqueness gives `x_{i+1} = x_i ⇔ α_i = 1` and `y_{i+1} = y_i ⇔ β_i = 1`.

*Step 5: the product conditions.*
- Apply `ρ_Y`. It fixes `α_i` and kills `β_i`. So `ρ_Y(g) = α_1α_2α_3`. This element lies in `F`, and also in
  `P_Z` by (L2), since `g ∈ P_X`. But `F ∩ P_Z = 1`, so `α_1α_2α_3 = 1` and `g ∈ N`.
- Put `β_3 := g^{-1} ∈ N`. Then `α_1β_1α_2β_2α_3β_3 = 1`.
- Also `y_3 = gα_3^{-1}A_Y = β_3^{-1}A_Y`.
- Apply `ρ_X`. It kills `α_i` and fixes `β_i`. So `β_1β_2β_3 = 1`.

*Converse.* Take any tuple satisfying the three conditions. The six cosets are consecutive neighbours: each
consecutive quotient lies in `F ⊂ P_Y` or in `N ⊂ P_X`. They all project to `x̄` or `ȳ`, so they form a
single-edge hexagon.

*Centres.* A vertex `uA_Y` is adjacent to `p_iA_X` iff `u ∈ p_iA_XA_Y`. Here `p_1 = 1`, `p_2 = α_1` and
`p_3 = α_1β_1α_2`. The target's reduction to type-`ŝ_4` upper bounds uses the fact that the links of the `ŝ_2`
and `ŝ_3` vertices are joins; that reduction is recorded on the target's Attempts. With it, the centre
criterion follows. ∎(A)

## (B) Blindness of `𝒜' = 𝒜_x ∪ 𝒜_y`

*Modularity.* `𝒜'∖𝒜_x = 𝒜_y∖𝒜_z` consists of 3 walls `H_1, H_2, H_3`. For each of the 3 pairs, the collision
normal `(b·ℓ_x)a − (a·ℓ_x)b` annihilates `ℓ_x`. It also annihilates `ℓ_y`, because `a, b ⊥ ℓ_y`. So it lies
in the 2-plane spanned by the roots of `𝒜_z`. `fibred.py` checks exactly (up to floating tolerance `1e-9`) that
it is proportional to a root of `𝒜_z`, for `H_3` and `H_4`. The log line is "(1)+(2) collisions of fibre
points lie on A_z walls: True".

So `ℓ_x` is modular, and (L3) gives `Q := π_1M(𝒜') = F_3 ⋊ P_X`. The section at infinity is the local
complement near `ℓ_x`, i.e. the image of `P_X` under (L1).

*The fibre group is `F`.* Take `v ∈ M(𝒜_x)`. The fibre over `v` is `(v + ℂℓ_x)∖{p_1,p_2,p_3}`, where
`p_j = v + t_j(v)ℓ_x` and `t_j(v) = −H_j(v)/H_j(ℓ_x)`. This is also the fibre over `v` of the fibration
`M(𝒜_y) → M(𝒜_z)/ℓ_x`. That fibration is the Fadell–Neuwirth fibration of Step 2, with fibre group
`F = ker ρ^Y_Z`.

Choose `v` near a generic point of `ℓ_y`. Then the whole fibre lies in `U_Y`, and the inclusion
`M(𝒜) ⊂ M(𝒜')` maps `F ⊂ P_Y ⊂ P` isomorphically onto the fibre group of `Q`. Write `x_1, x_2, x_3` for the
standard generators. So `Q = F ⋊ P_X`, and the quotient map `q : P → Q` is injective on `F` and on `P_X`.

*The monodromy factors through `ρ^X_Z`.* The fibre is classified by `v ↦ (t_1(v), t_2(v), t_3(v)) ∈ Conf_3(ℂ)`.
The `t_j` are linear, and they collide only on `𝒜_z` walls. So the classifying map extends over
`M(𝒜_z)/ℓ_x ⊇ M(𝒜_x)/ℓ_x`. Hence `μ_0 : P_X → P_3` factors through the map induced by
`M(𝒜_x) ⊂ M(𝒜_z)`, which is `ρ^X_Z`. In particular `μ_0(N) = 1`, so `[q(N), q(F)] = 1`.

*Conclusion.* In `Q`,
`α_1β_1α_2β_2α_3β_3 = (α_1α_2α_3)(β_1β_2β_3)`.
So the hexagon relation holds in `Q` for every tuple `α_i ∈ F`, `β_i ∈ N` that satisfies the two product
conditions.

For `ℬ ⊆ 𝒜'` we have `M(𝒜') ⊆ M(ℬ)`. So `π_1M(ℬ)` is a quotient of `Q`, and the same statement holds there.

Part (C) below produces tuples that satisfy both product conditions but violate the relation in `P`. Those
tuples are therefore not hexagons. No argument that uses the hexagon only through its image in `π_1M(ℬ)`, for
some `ℬ ⊆ 𝒜'`, can tell them apart from real hexagons.

*`H_3` calibration.* `fibred.py` and `augment.py` give the following counts for `H_3`:
- `|𝒜'| = 7`;
- 8 walls outside `𝒜'` pass through non-commuting flats `w ∩ w'`, with `w ∈ 𝒜_y∖𝒜_z` and `w' ∈ 𝒜_x∖𝒜_z`;
- 2 of the `I_2(5)` flats keep `ℓ_x` modular, with `|ℬ| = 10`.

Huang's auxiliary arrangement I (arXiv:2405.12068 §6) has 10 walls. It is of this `𝒜' ∪ 𝒜_V` form: it adds
the walls through such an `I_2(5)` point to the walls through `x̄` and `ȳ`. The wall count is consistent with
it, and so is the fact that Huang has to leave `𝒜'`. ∎(B)

## (C) The fibred augmentation `ℬ_V`

Let `V = w ∩ w'` be an `A_2` flat with `w ∈ 𝒜_y∖𝒜_z` and `w' ∈ 𝒜_x∖𝒜_z`. Its third wall `w''` lies outside
`𝒜'`. Set `ℬ_V = 𝒜' ∪ {w''}`, so `|ℬ_V| = 19`.

*Fibration.* `augment.py` checks, for all 9 such `V`, that the collision normal of each pair of
`ℬ_V∖𝒜_x = {H_1, H_2, H_3, w''}` is proportional to a root of `𝒜_x`. The log line is
`H4 type A2 |B| 19 fibre pts 4 l_x modular True collision walls outside A_z 3`. So by (L3):
- `G_V := π_1M(ℬ_V) = F_4 ⋊_μ P_X`, with `μ : P_X → P_4` and `p_4 = v + t_4(v)ℓ_x` the point on `w''`;
- forgetting `p_4` gives back the monodromy `μ_0` of (B), and `μ_0` factors through `ρ^X_Z`;
- so `μ(N) ⊆ ker(P_4 → P_3) = F_3`, which is the group that pushes `p_4` around `p_1, p_2, p_3` (Birman).

The three collisions `(p_i, p_4)` occur along 3 distinct walls `c_1, c_2, c_3 ∈ 𝒜_x∖𝒜_z`. The pairs `(p_i, p_j)`
with `i, j ≤ 3` only collide along walls of `𝒜_z`, so the logged count of 3 collision walls outside `𝒜_z`
means one wall for each pair `(i, 4)`.

*Lemma C1: `μ(N) ≠ 1`.*
- Let `m` be a meridian of `c_i` in `P_X`: a small loop around `c_i`, joined to the base point. Since
  `c_i ∉ 𝒜_z`, the loop bounds a disc in `M(𝒜_z)`. So `ρ^X_Z(m) = 1`, i.e. `m ∈ N`.
- `H_1(P_4) = ⊕_{i<j} ℤe_{ij}`, where `e_{ij}` records the winding number of `t_i − t_j`.
- The function `t_i − t_4` is a quotient of linear forms. On `M(𝒜_x)/ℓ_x` it vanishes to order one exactly
  along `c_i`. The other differences do not vanish along `c_i`.
- So `μ(m) ↦ e_{i4} ≠ 0` in `H_1(P_4)`. ∎

*Real base point and the image of `F`.* Take a real `v_0` in the open fundamental chamber, close to a generic
point `y_0` of the ray `ℓ_y`. The real points `v_0 + tℓ_x` with `t ≥ 0` stay in the open chamber, since the
chamber is a convex cone and `ℓ_x` is one of its rays.
- So all `t_j(v_0)` are real and negative.
- `t_1, t_2, t_3` are within `O(|v_0 − y_0|)` of `0`, because `H_j(y_0) = 0`. `t_4` is bounded away from `0`,
  because `w''(y_0) ≠ 0`.
- Take the global base point at `v_0 + Tℓ_x` with `T ≫ 1`. This point lies in `U_X`. The segment to `v_0`
  gives the standard embedding of `P_Y`, since it lies in the real chamber.

Let `D` be a small disc around `{p_1, p_2, p_3}` that misses `p_4`, joined to `+∞` along `ℝ_{>0}`. The fibre
`D∖{p_1,p_2,p_3}` lies in `U_Y`. Hence `q(F) = ⟨x_1, x_2, x_3⟩`, where
- `x_1, x_2, x_3, x_4` is a standard basis of `F_4 = π_1(fibre)`;
- `x_1x_2x_3 = ∂D`;
- the loop at infinity is `(x_1x_2x_3)x_4` or `x_4(x_1x_2x_3)`, depending on the orientation convention.

*Lemma C2: `[q(N), q(F)] ≠ 1` in `G_V`, and hence in `P`.* Take `n ∈ N` with `φ := μ(n) ≠ 1` (Lemma C1).
Suppose `φ` fixed `x_1, x_2, x_3`. By (L4) it also fixes the loop at infinity, and therefore fixes `x_4`. Then
`φ = id`. That is impossible, since `P_4` acts faithfully. So some `a ∈ F` has `φ(q(a)) ≠ q(a)`, i.e.
`[q(a), q(n)] ≠ 1`. ∎

*Lemma C3: the point-pushing identity.* The section at infinity is `q|_{P_X}`. So `q(β)fq(β)^{-1} = μ(β)(f)`
for `β ∈ P_X` and `f ∈ F_4`. Write `λ_i = μ(β_i) ∈ F_3` and use `β_1β_2β_3 = 1`. In `G_V`,

`q(α_1β_1α_2β_2α_3β_3) = q(α_1) · λ_1(q(α_2)) · (λ_1λ_2)(q(α_3))`.

So every single-edge hexagon satisfies `α_1 · Push_{λ_1}(α_2) · Push_{λ_1λ_2}(α_3) = 1` in `F_4`.

This is not automatic. The tuple `(α_1, α_2, α_3) = (a, a^{-1}, 1)`, `(β_1, β_2, β_3) = (n, n^{-1}, 1)` satisfies
both product conditions. For it the left side equals `a·φ(a)^{-1} ≠ 1`, with `a, n` taken from Lemma C2. So
this tuple is not a hexagon. It is exactly the kind of tuple that (B) shows `𝒜'` cannot see. ∎(C)

*`I_2(5)` variants.* For 3 of the `I_2(5)` flats `V` of the same shape, the same check gives modular `ℓ_x`:
`|ℬ_V| = 21`, 6 fibre points and 7 collision walls outside `𝒜_z`. Lemmas C1–C3 go through verbatim, with
`F_3 ⊂ P_4` replaced by the kernel of `P_6 → P_3`, which forgets the 3 new points.

## What this does not yet do

The target's Case 1 needs more than the identity: it needs a centre `uA_Y`. Huang's `H_3` argument turns the
analogous identity into a disc-diagram / Gauss–Bonnet contradiction in the Bass–Serre tree of a
graph-of-groups decomposition of the auxiliary group.

Here `G_V = F_4 ⋊_μ P_X`, and `P_X` (pure `H_3`) is not itself of fibre type, so there is no ready-made
linear graph of groups. The open step is one of two things:
- find a free splitting of `F_4` that is invariant under `μ(P_X)` (and respects `q(F) = ⟨x_1,x_2,x_3⟩`), and run
  Huang's Gauss–Bonnet argument in its Bass–Serre tree; or
- show directly that the point-pushing identity forces `Push_{λ_1}` to preserve `⟨x_1,x_2,x_3⟩`-cosets in a
  way that produces the centre (`y_2`, or some `s_4^kA_Y`, matching the w4-042 data).
