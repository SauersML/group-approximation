---
rg: 2
id: v-stabilized-horofunction-hosts-need-upstream-certification
kind: claim
title: "E3′ for hyperbolic seeds: the V-stabilized full group of a non-elementary hyperbolic group acting on its horofunction boundary is finitely presented; a finite shadow basis needs tiles whose deep windows certify their upstream, which half-trees have and ball patterns of horofunctions lack"
distinct_from:
  one-scale-filling-decides-fp-of-v-times-subshift-hosts: that states the one-scale criterion and the finite-shadow-basis mechanism, and names the seed compactifications' finite shadow bases as an unchecked condition (its Part 3); this isolates what that condition requires, shows why ball-pattern tiles of horofunctions fail it, and records the literature status.
  non-elementary-hyperbolic-groups-are-contracting-rsgs: that makes the UNSTABILIZED full group [[Γ | ∂_h Γ]] a full contracting RSG, hence finitely presented by Belk–Bleak–Matucci–Zaremsky; this is the V-stabilized group F(G_V × (Γ ⋉ ∂_h Γ)) that E3′ needs, which is not an RSG.
  cocompact-tree-end-shift-hosts-are-f-infinity: that is the tree calibration, where certification holds; this is the first carrier class where it fails.
---

**ESTABLISHED** for every Γ acting topologically freely on `∂_h Γ` whose full group `[[Γ | ∂_h Γ]]` is a full contracting RSG (for example every Γ with a proper Z free factor), by `v-stabilized-full-contracting-rsgs-are-finitely-presented` (bh-p2b-exact, 2026-09-18, lane proof, unreviewed), which closes the gap of item 4 below. Otherwise OPEN. This is E3′ (`v-times-rigid-topologically-free-sft-full-groups-are-fp`) for the hyperbolic seed
compactifications of `hyperbolic-groups-have-sft-horofunction-compactifications`, at the level of finite
presentation. Items 1–3 below are ESTABLISHED (lane proof, bh-p2b-exact, 2026-09-18, elementary; unreviewed).
Item 4 is a route with one named gap.

## Statement

Let `Γ` be non-elementary hyperbolic, let `∂_h Γ` be its horofunction boundary (the non-isolated part of `K_h`),
and let `𝒢 = Γ ⋉ ∂_h Γ`. Then `F(G_V × 𝒢)` is finitely presented.

The hyperbolic seeds are carriers: tree gluing turns them into minimal topologically free SFTs over `Γ ∗ Z`.
Through `one-scale-filling-decides-fp-of-v-times-subshift-hosts` Part 3, this statement is the first unchecked
condition for relative-seed gluings, which are the source of new Boone–Higman cases named there.

## 1. Literature status (read at source, `$GQ/src/bh-free-03/bbmz2-2309.06224.tex`)

- **Unstabilized: finitely presented.** BBMZ, arXiv:2309.06224:
  - Theorem l.176: every full, contracting RSG is finitely presented;
  - l.202–208: `[[Γ | ∂_h Γ]]` is one, whenever `Γ` has a proper `Z` free factor.

  The repo extends this to all non-elementary `Γ` (`non-elementary-hyperbolic-groups-are-contracting-rsgs`).
- **`F_∞` is open.** Question l.222, which is Nekrashevych's conjecture even for Röver–Nekrashevych groups.
- **The topological route failed for them.** l.225: an attempt "following a variant of the 'standard'
  approach … was unsuccessful, so it seems that some new ideas are needed."
- **The stabilized group is not covered.** A `G_V` germ `(uw, x) ↦ (u'w, x)` with `|u'| ≠ |u|` shifts one
  coordinate against the other. It is not a canonical similarity between cones of any synchronous product coding
  of `C × ∂_h Γ`, so `F(G_V × 𝒢)` is not an RSG in that coding, and BBMZ's theorem does not apply verbatim.

## 2. What a finite shadow basis needs: upstream certification

Take a family of clopen tiles whose splits are into Λ-translates of tiles (Part 2 of the one-scale node). The
split pieces of a tile `Y` are then translates `λY'` **contained in `Y`**. For compression codings, where one
refines by looking further along a descent, containment means the following.

> **(UC)** The deep window defining the smaller tile certifies the data defining the larger one, for **every**
> point of the smaller tile, not only for the points reached by descending from the larger tile's centre.

- **Trees satisfy (UC).** Put `∂H(e) = {ξ : the ray from o(e) to ξ crosses e}`. For an edge `e'` leaving
  `t(e)` with `e' ≠ ē`, `∂H(e') ⊆ ∂H(e)`: every `ξ ∈ ∂H(e')` has its ray from `o(e')` in the half-tree beyond
  `e'`, and in a tree the ray from `o(e)` is `e` followed by that ray. One edge gradient certifies the whole
  half-tree, because geodesics are unique.
- **Ball-pattern tiles of `K_h` do not satisfy (UC) through the squeeze.**
  - Let `T(h, Q) = {f : ∇f|_(B_k(h)) = Q}`.
  - The squeeze lemma of the horofunction node determines `f` on `B_k(g)` from its pattern on a deep window
    `W = B_k(γ(t))`, but only for `f` that has a descending ray from `g` into `W`. That condition lies outside
    `W`.
  - For an arbitrary `f'` with the same pattern on `W` and a fitting target `q`, the 1-Lipschitz bound only
    pins the upstream value to an interval. Here `w ∈ W` lies on a geodesic from `g` to `q`, which exists by the
    `13δ` bound:
    `d(g,q) + c − 2 d(g,w) ≤ f'(g) ≤ d(g,q) + c`.
  - So the split pieces are intersections `T(g,P) ∩ T(γ(t), Q)`, not translates of tiles.
  - This is the geometric content of Webster–Winchester non-merging: several descents from `g` need not share a
    tail.
- **The BBMZ coding certifies, but its translates are not tiles.** Cones `[w] ⊆ Σ_Γ` are nested by prefix, so
  (UC) is automatic. But `Γ` maps cones onto cones only through canonical similarities, up to its finite
  nucleus, not by global group elements. The split of `[w]` is into cones that are germ images, not
  `Γ`-translates. The obstruction therefore moves into the nucleus, which is where BBMZ's own topological attempt
  stopped.

## 3. Tree calibration inside the one-scale criterion

For a cocompact tree end shift, `F` is `F_∞` (`cocompact-tree-end-shift-hosts-are-f-infinity`, through Thumann).
So by the one-scale criterion the loops of any cocompact level of column partitions `[u] × ∂H(e)` die at some
larger level. The squares that the operad argument needs are the commutations of C-splits with tree splits. Each
lies inside one column, because a tree split of a column refines it rather than meeting it. That is where (UC)
enters. No explicit filling radius is claimed here.

With `v-times-gluing-presentations-are-exact` the same host has the explicit form `F = V(Λ) ∗_(V×Λ) N / ⟨⟨R_0⟩⟩`,
so its finite presentation is `V(Λ)`, finitely many gluing relators, and whatever presents `N_(∂T)`.

## 4. Route: vertical gluing over the full group (one gap)

Put `L = [[Γ | ∂_h Γ]]`. It is finitely presented, full and flexible, and acts faithfully on `X = ∂_h Γ`.
- **Pieces.** `A = V(L) = C(C, L) ⋊ V` and `B = LC(X, V) ⋊ L`, both acting faithfully on `C × X`, with
  `A ∩ B = V × L`. `A` is finitely presented for finitely presented `L` (`cantor-integer-maps-by-v-are-of-type-fp2`).
- **Generation.** `F(G_V × 𝒢) = ⟨A, B⟩`.
  - `L` is full, so a piece transposition `[u] × P ↔ [u'] × γP`, with `γ` a compact open bisection of `𝒢`,
    extends to `γ̂ ∈ L` whenever `P` and `γP` have nonempty complements.
  - Then the lift formula `γ̂|_([u])^(-1) (u u')^[γP] γ̂|_([u])` applies verbatim.
- **Exactness would follow from the room argument, except for one new relation family.**
  - The label `γ̂` is not unique: two extensions differ by some `μ ∈ L` fixing `P` pointwise.
  - Independence of the choice is the relation `[μ|_([u]), (u u')^[Q]] = 1` for `μ ∈ L` fixing `Q` pointwise.
  - These are disjoint in `C × X` but share the cone `[u]`, so neither (R1) nor the room lemma supplies them.
  - They are X-local labels against conditioned swaps. This is the vertical analogue of (R2), and it is the one
    gap.
- **What the route would give.** `F(G_V × 𝒢)` is finitely presented if:
  - (i) `B` is finitely presented. This is a Boolean-power piece, but over a *full* group, whose supports give
    room in `X` that `Λ` alone lacks;
  - (ii) the X-local label relations follow from finitely many.

  Neither is proved.

## Lesson for general BH

A finite shadow basis is **compression with upstream certification**. Refining along a descent must produce
translates that sit inside the tile, so the deep window has to certify where it came from. Trees certify with one
edge, because their geodesics are unique. Hyperbolic horofunctions do not: descents branch without merging, and
the deep window pins the upstream value only up to an interval. Symbolic codings certify by construction, but then
the group acts on cones only up to a nucleus. So for hyperbolic carriers the topological route to E3′ is blocked
at the same place as BBMZ's attempt at `F_∞`.

The algebraic route goes through the vertical gluing `V(L) ∗ (LC(X,V) ⋊ L)` over the full group `L`. It needs
one new relation family, X-local labels against conditioned swaps, and a Boolean power over a full group, where
fullness should supply the room in `X` that P2′a lacks over `Λ`.

## Referee (bh-ref-kourovka-b, 2026-09-18): items 1 and 3 PASS; item 2 PASS for trees but unproved for horofunctions; item 4 is a route

**Verdict** (the main statement is OPEN, as the node says).
- **Item 1: PASS.** I checked the literature status against the BBMZ TeX
  (`gq/src/bh-free-03/bbmz2-2309.06224.tex`):
  - Theorem A (full contracting RSGs are finitely presented);
  - `[[G | ∂_h G]]` is a full contracting RSG when `G` has a proper `Z` free factor;
  - the `F_∞` Question;
  - the sentence that their topological attempt "was unsuccessful".

  All are quoted correctly. The remark that the `G_V`-stabilized group is not an RSG in the synchronous
  product coding is plausible, and it is scoped to that coding.
- **Item 2: trees PASS; the horofunction half is a gap.**
  - (UC) for half-trees is correct: rays are unique, so `∂H(e') ⊆ ∂H(e)`.
  - For ball-pattern tiles of `K_h`, the node shows only that the squeeze and 1-Lipschitz bounds pin
    `f'(g)` to an interval of length `2d(g,w)`. That shows the squeeze argument cannot certify (UC).
    It does not show that split pieces fail to be translates.
  - For the stronger sentence ("the split pieces are intersections …, not translates of tiles"),
    exhibit `f, f' ∈ ∂_h Γ` with equal gradients on an arbitrarily deep window `W` along a descent
    from `g` and different gradients on `B_k(g)`. Webster–Winchester non-merging suggests such a pair,
    but it is not written. Until then, read item 2 as "the squeeze does not certify (UC)".
- **Item 3: PASS as a consequence** of the cited `F_∞` and one-scale nodes, with no filling radius
  claimed.
- **Item 4** is correctly labelled a route. Its gaps are named precisely: (i) finite presentation of
  `B = LC(X, V) ⋊ L`, and (ii) the `X`-local label relations `[μ|_{[u]}, (u u')^{[Q]}] = 1`.
