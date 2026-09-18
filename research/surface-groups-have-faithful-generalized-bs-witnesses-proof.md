---
rg: 2
id: surface-groups-have-faithful-generalized-bs-witnesses-proof
kind: route
title: The norm-one group of a Z[1/5]-order in an indefinite division quaternion algebra is a faithful surface-type tree lattice
target: surface-groups-have-faithful-generalized-bs-witnesses
requires: []
artifacts:
  - research/artifacts/gq-bh-bh-free-extensions-bliw-section-11-12.md
---

Notation as in the claim: `D` of discriminant `6`, `O` maximal, `p = 5`, `Λ = (O[1/5])^1`, and
`T` the Bruhat–Tits tree of `SL_2(Q_5)`.

**Textbook inputs, stated and not re-read at source:**
- (a) `D ⊗ R ≅ M_2(R)` and `D ⊗ Q_5 ≅ M_2(Q_5)`, since `D` is ramified only at 2 and 3.
- (b) `Λ` embeds diagonally as a lattice in `SL_2(R) × SL_2(Q_5)`, and it is cocompact because `D`
  is a division algebra (Borel–Harish-Chandra; Godement's compactness criterion).
- (c) `SL_2(Q_5)` acts on `T` without inversions, and the kernel of the action is `{±1}` (Serre,
  *Trees*, II.1).
- (d) For a vertex `v` of `T`, `Stab_{SL_2(Q_5)}(v)` is compact open, and the vertex and edge
  stabilizers in `Λ` are the norm-one groups of the maximal and Eichler `Z`-orders cut out by `v`
  and `e` (Vignéras, Ch. IV; Serre, *Trees*, II.1.4).
- (e) A finitely generated Fuchsian group has a torsion-free subgroup of finite index (Selberg). A
  torsion-free cocompact Fuchsian group is `π_1` of a closed orientable surface of genus `≥ 2`.

**Steps.**
1. **Faithful.** Let `λ ∈ Λ` act trivially on `T`. By (c) its image in `SL_2(Q_5)` is `±1`. The map
   `Λ -> SL_2(Q_5)` is injective, because `Λ ⊂ D^×` and `D -> D ⊗ Q_5` is injective. So `λ = ±1`,
   and `Λ̄ = Λ/{±1}` acts faithfully. It acts without inversions by (c).
2. **Finitely many orbits.** Take a compact `C ⊂ SL_2(R) × SL_2(Q_5)` with `ΛC` the whole group,
   by (b). The `SL_2(Q_5)`-projection of `C` moves a fixed vertex `v_0` to finitely many vertices,
   since vertex stabilizers are open and `C` is compact. `SL_2(Q_5)` has two vertex orbits on `T`,
   so `Λ` has finitely many vertex orbits, and likewise finitely many edge orbits.
3. **Vertex groups.** `Λ_v = Λ ∩ (SL_2(R) × Stab(v))` projects injectively to a discrete subgroup of
   `SL_2(R)`, because `Stab(v)` is compact. It is cocompact there, because `Λ` is cocompact and
   `Stab(v)` is open. So `Λ̄_v` is a cocompact Fuchsian group (d). By (e) it contains a closed
   surface group of genus `≥ 2` with finite index.
4. **Commensurability.** Closed surface groups `π_1(S_g)` and `π_1(S_h)` with `g, h ≥ 2` have
   isomorphic subgroups of index `h-1` and `g-1` respectively: both have genus `(g-1)(h-1)+1`,
   by the Euler characteristic of covers. Non-orientable closed surfaces with `χ < 0` are doubly
   covered by orientable ones. So all these groups, all the `Λ̄_v`, and any group commensurable
   with a cocompact Fuchsian group are pairwise abstractly commensurable.
5. **Edge groups.** `T` is `6`-regular, so `[Λ̄_v : Λ̄_e] ≤ 6` for `e` incident to `v`.
6. **Conclusion.** By the Bass–Serre structure theorem, `Λ̄` is the fundamental group of the finite
   quotient graph of groups `Λ̄\T`. Its vertex and edge groups are commensurable with `G` (steps 3–5),
   and its edge inclusions have finite index. So `Λ̄ ∈ BS_G`. It is nontrivial and acts faithfully
   on its Bass–Serre tree, which is `T` (step 1).

**Trust surface:** inputs (a)–(e) only. Nothing from Bux–Llosa Isenrich–Wu is used here; their
Theorem 11.1 consumes this witness in
`surface-generalized-bs-groups-satisfy-boone-higman`.
