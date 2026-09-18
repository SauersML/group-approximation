---
rg: 2
id: rank-two-building-non-domesticity-is-vertex-non-domesticity
kind: claim
title: For rank-two Euclidean buildings, non-domesticity at infinity is a condition on vertices at infinity - topological freeness for products of trees and Ã₂, non-opposition sets for C̃₂ and G̃₂ - giving one MIF and B_A criterion for fp simple lattices
distinct_from:
  titz-witzel-kernel-elements-are-nowhere-domestic-at-infinity: that is the chamber-level crux for the Titz Mite–Witzel kernels; this reduces the chamber-level condition, for every rank-two Euclidean building, to a condition on each type of vertex at infinity, and identifies it with topological freeness when the polygon at infinity is a digon or a projective plane.
  opposition-general-position-from-nowhere-domestic-dense-poles: that turns chamber non-domesticity and dense poles into general position; this supplies the vertex form of its hypothesis (D1).
  product-of-trees-lattices-with-faithful-factor-satisfy-pbh: that reaches product-of-trees lattices through Bass–Serre theory; this gives a second, dynamical route (MIF), which also applies when no tree factor is present.
artifacts:
  - research/artifacts/gq-bh-bh-testcases-ranking.md
---

**ESTABLISHED** (lane proof, elementary modulo the standard facts (V1)–(V3); not
independently reviewed; no priority claimed).

## Setting

- `X` is a locally finite thick Euclidean building of dimension 2. Its building at infinity
  `∂X` is a generalized `m`-gon:
  - `m = 2` for products of two trees;
  - `m = 3` for `Ã₂`;
  - `m = 4` for `C̃₂`;
  - `m = 6` for `G̃₂`.
- Chambers at infinity are flags `c = (ξ_1, ξ_2)`, where `ξ_i = π_i(c)` is the vertex of
  type `i`. `Z = Ch(∂X)` and the vertex spaces `∂X_i` carry the cone topology.
- `g` is a type-preserving automorphism. Put
  - `N(g) = {c ∈ Z : gc not opposite c}`;
  - `N_i(g) = {ξ ∈ ∂X_i : gξ not opposite ξ}`.

  For `m` odd, opposite vertices have different types.

Standard facts used, not re-proved:
- **(V1)** `π_i : Z → ∂X_i` is continuous, open and surjective.
- **(V2)** For every vertex `ξ` at infinity, the fibre `π^-1(ξ)` of chambers containing `ξ`
  is homeomorphic to the end space of the panel tree of `ξ`, a thick locally finite tree.
  So it is perfect.
- **(V3)** Two flags of a generalized `m`-gon are opposite exactly when:
  - for `m` even, both pairs of vertices of equal type are opposite;
  - for `m` odd, each vertex of one flag is opposite the vertex of the other type in the
    other flag, which for a projective plane means `p ∉ L'` and `p' ∉ L`.

## Statement

1. **Even `m` (products of trees, `C̃₂`, `G̃₂`).**
   `N(g) = π_1^-1(N_1(g)) ∪ π_2^-1(N_2(g))`. So `N(g)` has empty interior iff both `N_1(g)`
   and `N_2(g)` have empty interior.
2. **Products of trees (`m = 2`).** Vertices at infinity of type `i` are the ends of `T_i`,
   and they are opposite iff distinct. So `N_i(g) = Fix(g_i) ⊆ ∂T_i`. Hence `N(g)` has
   empty interior iff neither coordinate `g_i` fixes a nonempty open set of ends.
3. **`Ã₂` (`m = 3`).** `N(g)` has nonempty interior iff `g` fixes pointwise a nonempty open set
   of vertices at infinity of one type.
4. **The MIF and `B_A` criterion.** Let `S` be a finitely presented simple group acting
   properly and cocompactly on `X` by type-preserving automorphisms. Suppose:
   - **(D2)** pole pairs of strongly regular elements of `S` are dense in the opposition
     relation `O`;
   - **(D1v)** for every `g ∈ S ∖ {1}` and each type `i`, `N_i(g)` has empty interior. For
     `m ∈ {2, 3}` this means `S` acts topologically freely on both vertex spaces at
     infinity.

   Then `S` is mixed-identity-free and `S ∈ B_A`.

## Proof

**Item 1.** By (V3), and because `g` preserves types, `c ∈ N(g)` iff `gξ_1` is not opposite
`ξ_1` or `gξ_2` is not opposite `ξ_2`. That is the displayed union.
- If `N_i(g)` contains a nonempty open set `W`, then `π_i^-1(W)` is nonempty (π_i is
  surjective), open, and contained in `N(g)`.
- Conversely, suppose `N(g)`, which is closed, contains a nonempty open `V`. The sets
  `V ∩ π_i^-1(N_i(g))` are closed in `V`, and they cover it. Since `V` is Baire, one of them
  contains a nonempty open `V'`. Then `π_i(V') ⊆ N_i(g)` is open by (V1).

**Item 2.** In `T_1 × T_2`, opposite chambers at infinity are pairs of ends that differ in
both coordinates. So vertices of the same type are opposite iff distinct, and item 1
applies.

**Item 3.** By (V3), `c = (p, L) ∈ N(g)` iff `gp ∈ L` or `p ∈ gL`.
- **⇐.** If `g` fixes every point of an open `W ⊆ ∂X_1`, then `π_1^-1(W) ⊆ N(g)`, since
  `gp = p ∈ L`. Lines are symmetric.
- **⇒.** Let `V ⊆ N(g)` be nonempty and open. As in item 1, Baire gives a nonempty open
  `V' ⊆ V` on which, say, `gp ∈ L` holds throughout. Fix `p ∈ π_1(V')`.
  - The fibre `{L : (p, L) ∈ V'}` is a nonempty open subset of `π_1^-1(p)`. By (V2) it is
    infinite.
  - If `gp ≠ p`, exactly one line contains both `p` and `gp`, which is a contradiction.
  - So `g` fixes every point of the open set `π_1(V')`, by (V1). The case `p ∈ gL` gives
    fixed lines symmetrically, since `p = L ∩ gL` is forced when `gL ≠ L`.

**Item 4.** Neither torsion-freeness nor irreducibility is assumed. The proof uses only:
- `strongly-regular-building-elements-are-opposition-proximal` (ESTABLISHED) gives
  compactness, openness and density of `O`, and makes strongly regular elements proximal.
- (D2), together with items 1 and 3, gives the hypotheses (D1) and (D2) of
  `opposition-general-position-from-nowhere-domestic-dense-poles`. So (GP) holds, and
  `opposition-ping-pong-criterion-gives-mixed-identity-freeness` makes `S` MIF.
- BFFHZ Theorem C (iv)⇒(i) (`fp-simple-highly-transitive-groups-satisfy-pbh`) puts the
  finitely presented simple MIF group `S` in `B_A`. ∎

## Consequences and scope

- **One theorem, three families.**
  - Burger–Mozes, Wise and Rattaggi-type simple lattices in products of trees need only
    topological freeness of both projections on tree boundaries. For Burger–Mozes groups,
    BFFHZ Remark 3.5 is reported to prove this (web summary; not read at source).
  - Simple lattices in exotic `Ã₂` buildings, if any exist, need topological freeness on
    points and lines at infinity.
  - The Titz Mite–Witzel kernels (`C̃₂`) need the non-opposition form below.
- **The `C̃₂` crux, sharpened.** For the Titz Mite–Witzel kernels,
  `titz-witzel-kernel-elements-are-nowhere-domestic-at-infinity` is equivalent to:
  > no nontrivial `g ∈ Γ̌` maps a nonempty open set of points at infinity to collinear or
  > equal points, and none maps a nonempty open set of lines to concurrent or equal
  > lines.

  That is local point- or line-domesticity, the local form of the ovoid and spread
  collineations of Neyt–Parkinson–Van Maldeghem. So it is more than a fixed-point
  condition. The panel-tree formulation proposed earlier is **not** the right
  generalization in `C̃₂`: the ends of one panel tree form a closed nowhere dense subset
  of `∂X_i`. The vertex spaces themselves are the right objects. The two formulations
  coincide only for products of trees, where every panel tree is a factor.
- **Not claimed.** (D2) and (D1v) are not proved for any exotic lattice here.

## Lesson for general BH

In every rank-two building, the lattice-specific input to the higher-rank MIF, and
hence `B_A`, criterion is a property of the action on the **vertex spaces at infinity**.
- It is exactly topological freeness when the polygon at infinity is a digon or a
  projective plane, which is the rank-one condition of Rybak and Hull–Osin applied to
  each type of vertex.
- In quadrangles and hexagons it is freeness from local point- and line-domesticity.

So "higher-rank BH via MIF" is a transfer of the rank-one boundary criterion, type by
type. Its only genuinely new obstruction is the polygon-specific domesticity
phenomenon, which does not occur for `m ≤ 3`.
