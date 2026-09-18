---
rg: 2
id: ore-operad-groups-contain-the-derived-full-group
kind: claim
title: A dissection-operad group with Ore's condition that contains a germ-generating subgroup contains the derived subgroup of the whole full group, hence every perfect subgroup of it
distinct_from:
  transvections-are-single-carets-of-the-edge-split-operad: that puts the linear group itself inside the edge-split operad group; this upgrades any germ-generating subgroup to the whole derived full group, so perfect groups such as closed mapping class groups need no coding of their own.
  closed-mcg-embeds-in-rational-projective-full-group: that embeds the mapping class group in the full group of all integral projective germs; this shows that, under Ore's condition, a much smaller finitely generated operad group already contains it.
  perfect-subgroups-are-locally-trivial-in-abelian-germ-hosts: that is an obstruction for hosts with torsion-free abelian point germs; this is a containment theorem for hosts whose germ groupoid is purely infinite and minimal, where germs are typically nonabelian.
---

**ESTABLISHED** (lane bh-free-54, 2026-09-18), modulo Matui's normal-subgroup theorem.
That theorem is recalled and was not re-read at source. The rest is a lane proof, not
independently reviewed.

## Setting

- **The groupoid.** `𝒢` is an effective ample groupoid on a Cantor space `X`. It is
  minimal and purely infinite: every clopen `A` contains disjoint clopens `A_1, A_2`
  that are `𝒢`-equivalent to `A`.
- **The operad.** `𝒪` is a dissection operad on compact open tiles covering `X`, as
  in `non-lcm-dissection-operad-groups-are-f-infinity`. Its fractions act on `X` by
  `𝒢`-local homeomorphisms.
  - Assume `𝒪` satisfies Ore's condition. Then its fractions `θ'∘θ^{-1}` form a group
    `G_𝒪 ≤ [[𝒢]]`.
  - A clopen is *accessible* if it is a union of pieces of some `𝒪`-dissection
    (family) of `X`.
- **Assumptions.**
  - **(i)** Some subgroup `Γ ≤ G_𝒪` is germ-generating: every germ of `𝒢` is a germ
    of an element of `Γ`.
  - **(ii)** The `Γ`-translates of `𝒪`-pieces form a basis of `X`.

## Statement

1. `G_𝒪` contains every *swap* `τ_{U,V,φ}`. Here `U, V` are disjoint clopens,
   `φ : U → V` is a `𝒢`-local homeomorphism, and `τ` is `φ` on `U`, `φ^{-1}` on `V`,
   and the identity elsewhere.
2. Hence `G_𝒪 ⊇ D([[𝒢]])`, and `G_𝒪` contains every perfect subgroup of `[[𝒢]]`.

## Proof

1. **Reduction to basic pieces.**
   - Refine `U` into basic clopens `U_k = γ_kN_k` (`γ_k ∈ Γ`, `N_k` an `𝒪`-piece) on
     each of which `φ` agrees with some `h_k ∈ Γ`. This uses (i) and (ii).
   - Then `τ_{U,V,φ} = ∏_k τ_{U_k, h_kU_k, h_k}`, a product of commuting swaps with
     disjoint supports.
   - So it suffices to treat `τ = τ_{U,V,h}` with `U = γN` and `V = hU`.
2. **Making `U` and `V` unions of pieces.**
   - Under Ore's condition, `γ` and `h` are single fractions. Say `h` maps an
     `𝒪`-dissection `A` onto `hA`.
   - `N` is a union of pieces of an `𝒪`-dissection `B`. Refine `B` so that `γ` is
     defined on it as a fraction. Then `U` is a union of pieces of `C_1 = γB`.
   - Take a common refinement `C = C_1∘α = A∘β` (Ore). Then `U` is a union of
     `C`-pieces, and `V = hU` is a union of pieces of `hC = hA∘β`, which is again an
     `𝒪`-dissection.
3. **Matching the two sides.**
   - Let `C'` be a common refinement of `C` and `hC` (Ore).
   - Each `C`-piece `M ⊂ U` is refined in `C'` by some `μ_M ∈ 𝒪`. Its image `hM` is
     refined by some `μ'_M`.
   - Pick `ν_M` refining both `μ_M` and `μ'_M` (Ore, in the piece's own frame). Refine
     `C'` by `ν_M` on `M` and on `hM`, for every `M`. `U` and `V` are disjoint, so there
     is no conflict.
   - In the result `C''`, `τ` maps the pieces `M∘ν_M` to `hM∘ν_M`, and back, with
     matching labels. So `τ` is the relabelling fraction `C'' ↦ C''`, and `τ ∈ G_𝒪`.
4. **From swaps to the derived subgroup.**
   - A conjugate of a swap by an element of `[[𝒢]]` is again a swap. So the swaps
     generate a nontrivial normal subgroup `S ⊴ [[𝒢]]`, and `S ≤ G_𝒪`.
   - For minimal purely infinite effective ample groupoids on a Cantor space,
     `D([[𝒢]])` is simple. This is Matui, *Topological full groups of one-sided
     shifts of finite type*, J. reine angew. Math. 2015, Theorem 4.16; recalled, not
     re-read. Only simplicity is used.
   - `S ∩ D([[𝒢]])` is normal in `D([[𝒢]])`, and it is nontrivial.
     - Take swaps `τ_1, τ_2 ∈ S` whose supports overlap without being equal. Then
       `[τ_1, τ_2] ≠ 1`.
     - This commutator lies in `D([[𝒢]])`, and in `S` because `S` is normal.
   - Simplicity then gives `D([[𝒢]]) ≤ S ≤ G_𝒪`. A perfect subgroup `L` satisfies
     `L = [L, L] ≤ D([[𝒢]])`.

## Instances

- **The integral projective host** (`closed-mcg-embeds-in-rational-projective-full-group`).
  - `𝒢 = GL_{m+1}(Z) ⋉ Ŝ_m` is minimal and purely infinite (its proof, §4).
  - For `𝒪 = 𝒪_E`, the edge-split operad, `Γ = GL_{m+1}(Z)` lies in `G_𝒪`
    (`transvections-are-single-carets-of-the-edge-split-operad`). It is germ-generating
    by definition.
  - Translates of the orthants form a basis, since unimodular cones do.
- **The conclusion.** If `𝒪_E` satisfies Ore's condition in rank `m + 1`, then
  `G_E ⊇ D(𝒯_m)`. So:
  - `Mod(S_g) ≤ G_E` for `m = 6g − 7`, `g ≥ 3`, since `Mod(S_g)` is perfect (Powell;
    recalled);
  - `SL_{m+1}(Z) ≤ G_E` for `m ≥ 2`.
- **What is no longer needed.** Neither train-track moves nor Dehn twists need to be
  coded as carets. Nor must `G_E` equal `𝒯_m`.
- **The perfect-subgroup lemma of lane bh-free-51.** Point germs of `G_E` are full
  point stabilizers in `GL_{m+1}(Z)`, since the action is topologically free. At a
  point over a rational ray with a chosen flag direction, the stabilizer contains the
  integral Heisenberg group, which is nonabelian. So
  `perfect-subgroups-are-locally-trivial-in-abelian-germ-hosts` does not apply, as
  that node itself notes for `𝒯_m`.

## Lesson for general BH

- **The group itself need not be coded.** For a perfect group `L` inside a purely
  infinite minimal full group `[[𝒢]]`, a Thompson-like host need not realize `L` at
  all. It needs:
  - Ore's condition;
  - one germ-generating subgroup, which can be chosen for convenience (here the
    linear group, acting by single carets).
- **Consequence.** The Serret-type coding gate for `L` disappears for perfect `L`,
  and what remains is purely operad-theoretic: Ore's condition, finite type, and the
  type (A) action of `ore-operad-groups-have-type-a-clopen-actions`.
- **Non-perfect inputs.** For non-perfect `L`, pass to a perfect subgroup or to
  `L ∩ D([[𝒢]])` first.
