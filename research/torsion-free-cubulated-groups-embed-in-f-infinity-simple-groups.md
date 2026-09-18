---
rg: 2
id: torsion-free-cubulated-groups-embed-in-f-infinity-simple-groups
kind: claim
title: Every group acting freely and cocompactly on a CAT(0) cube complex embeds in a simple group of type F_infinity, so every virtually torsion-free cubulated group embeds in a finitely presented simple group (would answer BBCMP Question 1.15)
requires:
  - flagged-pointed-cube-category-resynchronizes-cubulated-actions
  - cuntz-stabilized-garside-full-groups-are-f-infinity
  - cuntz-stabilized-minimal-full-groups-are-acyclic-and-simple
  - matui-purely-infinite-minimal-full-groups-have-simple-d
  - matui-groupoid-homology-kunneth-and-full-shift-vanishing
distinct_from:
  virtually-torsion-free-cubulated-groups-satisfy-boone-higman: that is the open question node (BBCMP Q1.15); this is the claimed answer, with its proof chain.
  cubulated-hyperbolic-groups-are-virtually-special: that covers hyperbolic cubulated groups via Agol; this needs no hyperbolicity, specialness or residual finiteness.
  cocompact-tree-product-lattices-lie-in-type-a-class: that is the product-of-trees case; this is every cubulation.
---

**OPEN — proof claimed 2026-09-18, not independently reviewed.** The complete lane chain
is in `torsion-free-cubulated-f-infinity-simple-host-proof`. Every link is either a landed
lane node or an import quoted on main. Do not cite this as established until two
independent checks pass. The weakest links are:
- Li's link lemma, read over `Γ(*)` (§8 of `cuntz-stabilized-garside-full-groups-f-infinity-proof`);
- the Garside verification for the flagged category.

Priority: a bounded web search (2026-09-18) found no prior statement.

## Statement

1. **Torsion-free case.** Let `G` act freely and cocompactly on a CAT(0) cube complex `X`.
   Then `G` embeds in a simple group `S` of type `F_∞`.
2. **Virtually torsion-free case.** Every virtually torsion-free group acting properly and
   cocompactly on a CAT(0) cube complex embeds in a finitely presented simple group (type
   `F_∞`). This answers BBCMP Question 1.15 positively, if the proof stands.

## The host

1. **Stabilize by free loops.**
   - Let `K = X/G`, and let `K'` be `K` with one loop `c_v` attached at every vertex `v`.
   - Then `G' = π_1 K' = G * F_r`, and its universal cover `X'` is a tree of copies of `X`
     joined by `c`-edges at every vertex.
   - `G'` acts freely and cocompactly on `X'`, and `G ≤ G'`.
2. **Flag the coding.** Let `C⁺ = C⁺_{X'}` be the flagged pointed-cube category of
   `flagged-pointed-cube-category-resynchronizes-cubulated-actions`, `𝒢⁺ = I_l ⋉ ∂Ω(C⁺)`,
   and `Y ≅ ∂_R X'` its base cone. Every `g ∈ G'` is a global bisection of `𝒢⁺|_Y`.
3. **Stabilize by Cuntz.** `S = F((𝒢⁺ × G_2)|_{Y × {x,y}^ℕ})`, and `G' ↪ S` by
   `g ↦ g × id`.

## Why each gate holds for `X'`

- **(TF) and faithfulness.** Every nonempty open subset of `∂_R X'` contains points that
  leave through a `c`-edge and realize every end of a half-tree of the tree of copies. An
  element fixing it fixes a `c`-edge, and `c`-edge stabilizers are trivial.
- **(G2), i.e. (Acyc).** Every open set contains a point that leaves, through a fresh
  `c`-edge, into a branch avoiding the end of any given periodic ray. So nothing open lies
  beyond a loop.
- **(G3), by minimality.**
  - Any object reaches any other by fresh `c`-edges and one flag, so `𝒢⁺|_Y` is minimal.
  - The Cuntz factor makes the product purely infinite minimal, hence it has comparison.
  - `H_*(· × G_2) = 0`.
  - So Li's Corollary D makes `S` perfect and acyclic, and Matui's theorem makes
    `D(S) = S` simple.
- **(G1).** It holds by the flag theorem.

## Lesson for general BH

For cubulated groups the whole Boone–Higman problem split into three independent mechanisms:
- **flags** repair resynchronization;
- **the Cuntz factor** repairs merge packing, and with it finiteness;
- **free loops at every vertex** repair dynamics: topological freeness, no trapped open
  sets, and minimality.

None of these uses specialness, hyperbolicity or residual finiteness. So the template
"geodesic coding + flags + Cuntz + free loops" should apply to any group acting
geometrically on a space whose geodesics admit a finite local-state median coding.
