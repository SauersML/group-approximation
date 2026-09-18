---
rg: 2
id: edge-split-ore-iff-synchronization-and-tree-domination
kind: claim
title: Ore's condition for the edge-split operad is equivalent to synchronization of descendants plus tree domination of descendant dissections, and these two give the whole rational projective full group as the edge-split group
requires:
  - edge-splits-cut-every-rational-hyperplane
distinct_from:
  edge-split-operad-has-common-refinements: that is Ore's condition, still open; this proves it is equivalent to two separate statements, one pointwise and Diophantine and one combinatorial, for every m.
  unimodular-cells-synchronize-under-edge-splits: that is the synchronization half (Sync_m); this shows what else Ore needs, namely tree domination, and that nothing more is needed.
  edge-split-order-is-not-geometric-refinement: that shows the geometric shortcut to Ore fails; this is the replacement reduction.
---

**ESTABLISHED** (lane bh-free-54, 2026-09-18). Lane proof, elementary, not
independently reviewed. It holds for every `m ≥ 1`.

## Notation

- **Cells.** A *cell* is a unimodular simplicial cone `cone(F)`, `F ∈ GL_{m+1}(Z)`.
  `Desc(C)` is its set of iterated edge-split descendants, and `Trees(C)` its set of
  edge-split dissections (split trees).
- **Order.** `D ≥_E D'` means `D|p ∈ Trees(p)` for every piece `p` of `D'`.
  This order is transitive (operad composition).
- **Descendant dissections.** A *descendant dissection* of `C` is a finite dissection
  of `C` (T-junctions allowed) into cells of `Desc(C)`. Every split tree of `C` is one.
- **(Sync′)** For all `p, q ∈ Desc(Δ)` with overlapping interiors, `p ∩ q` has a
  dissection into cells of `Desc(p) ∩ Desc(q)`.
- **(TD) Tree domination.** For every cell `C` and every descendant dissection `D` of
  `C`, some `T ∈ Trees(C)` refines `D` with `T|r ∈ Trees(r)` for each `r ∈ D`.
  By `GL_{m+1}(Z)`-equivariance, it is enough to take `C = Δ`.
- **(Ore)** Any two elements of `Trees(Δ)` have a common `≥_E`-upper bound. This is
  `edge-split-operad-has-common-refinements`.

## Statement

1. **Equivalence.** `(Ore) ⟺ (Sync′) ∧ (TD)`.
2. **Synchronization.** `(Sync_m)` (`unimodular-cells-synchronize-under-edge-splits`)
   implies `(Sync′)`.
3. **Saturation.** `(Sync_m) ∧ (TD)` implies that every unimodular dissection `D` of
   `Δ` is dominated: some `T ∈ Trees(Δ)` has `T|r ∈ Trees(r)` for all `r ∈ D`. Hence
   the edge-split operad group is the whole full group: `π_1(𝒪_E, Δ) = [[𝒢|_Δ]] ≅ 𝒯_m`.
4. **Atoms suffice.** (Ore) holds if and only if every `T ∈ Trees(Δ)` and every single
   edge split `E_a` of `Δ` have a common `≥_E`-upper bound (Ore_atom).

## Proofs

**1, (⇐).** Let `A, B ∈ Trees(Δ)`.
- **A common geometric refinement by common descendants.** For `p ∈ A` and `q ∈ B`
  with overlapping interiors, `p, q ∈ Desc(Δ)`. So (Sync′) gives a dissection of
  `p ∩ q` into cells of `Desc(p) ∩ Desc(q)`. Together these form a dissection `D` of
  `Δ`. Each `r ∈ D` lies in `Desc(p) ∩ Desc(q)` for the pieces `p ∋ r` of `A` and
  `q ∋ r` of `B`.
- **Above `A`.** For `p ∈ A`, `D|p` is a descendant dissection of `p`. (TD) gives
  `T_p ∈ Trees(p)` refining it, with `T_p|r ∈ Trees(r)`. Then `T = ⋃ T_p ∈ Trees(Δ)`
  and `T ≥_E A`.
- **The `B` side.** For `q ∈ B`, every piece `s` of `T|q` lies in some `r ∈ D` with
  `r ⊆ q`, and `s ∈ Desc(r) ⊆ Desc(q)`. So `T|q` is a descendant dissection of `q`.
  (TD) gives `U_q ∈ Trees(q)` refining it, with `U_q|s ∈ Trees(s)`. Put
  `U = ⋃ U_q ∈ Trees(Δ)`. Then `U ≥_E B`.
- **Above both.** For `s ∈ T`, `U|s = U_q|s ∈ Trees(s)`, so `U ≥_E T ≥_E A`, and by
  transitivity `U ≥_E A`.

**1, (⇒).** Every `p ∈ Desc(Δ)` is a piece of its *path tree*: `p` together with
the siblings along one descent path.
- **(Sync′).** Let `U` be a common upper bound of path trees containing `p` and `q`.
  Then `U|p ∈ Trees(p)` and `U|q ∈ Trees(q)`. The pieces of `U` inside `p ∩ q` lie in
  `Desc(p) ∩ Desc(q)` and tile it.
- **(TD).** Given a descendant dissection `D` of `Δ`, let `U` be a common upper bound
  of the path trees of all `r ∈ D` (iterate (Ore) finitely often). Then `U` refines
  `D` and `U|r ∈ Trees(r)`.

**2.** Let `p, q ∈ Desc(Δ)` overlap.
- The cut lemma of `edge-splits-cut-every-rational-hyperplane`, applied to the facet
  forms of `q`, gives a split tree of `p` each of whose pieces `p'` lies in `q` or
  meets it only in walls.
- For each `p' ⊆ q`, (Sync_m) gives a dissection of `p'` into cells of
  `Desc(p') ∩ Desc(q) ⊆ Desc(p) ∩ Desc(q)`. "Finite union up to walls" is made
  disjoint with the cut lemma, as in the local form of that node.

**3.** Let `D` be any unimodular dissection of `Δ`.
- **Descendant pieces.** For `r ∈ D`, (Sync_m) for `r ⊆ Δ` gives a dissection `D_r` of
  `r` into cells of `Desc(r) ∩ Desc(Δ)`. (TD) for `(r, D_r)` gives `S_r ∈ Trees(r)`
  whose pieces lie in `Desc(Δ)`.
- **Domination.** So `D' = ⋃ S_r` is a descendant dissection of `Δ` with
  `D'|r ∈ Trees(r)`. (TD) for `(Δ, D')` gives `T`, and `T|r ∈ Trees(r)` by
  composition.
- **Saturation.** Let `g ∈ [[𝒢|_Δ]]` map the pieces of `D` by `g_r ∈ GL_{m+1}(Z)`
  onto those of `D''`, and let `T` dominate `D`.
  - By equivariance, `g(T)` refines `D''` and `g(T)|g_r r = g_r(T|r)` is a split tree
    of `g_r r`.
  - Let `T'` dominate `g(T)`. Then `g^{-1}(T')` refines `T` with a split tree on each
    piece, so `g^{-1}(T') ∈ Trees(Δ)`.
  - `g` maps each piece `x` of `g^{-1}(T')` onto a piece of `T'` by an element of
    `GL_{m+1}(Z)`. Frames of cells are unique up to a column permutation, so this
    element is `frame(g x) P frame(x)^{-1}` for a permutation matrix `P`.
  - So `g` is the fraction `T' ∘ (g^{-1}T')^{-1}` with transformation labels `P`, an
    element of `π_1(𝒪_E, Δ)`.

**4.** Only (⇐) needs proof. Induct on `|B|` to get a common upper bound of `A` and `B`, for all `A`.
- If `B = Δ`, take `A`. Otherwise `B = E_b ∘ (B_1, B_2)`, with `B_1, B_2` split trees of the
  children `C_b^±`.
- (Ore_atom) gives `U ≥_E A, E_b`, so `U|C_b^± ∈ Trees(C_b^±)`.
- The induction hypothesis in the frame of `C_b^+` gives `V_1 ≥_E U|C_b^+, B_1`, and likewise `V_2`.
  Then `V = V_1 ∪ V_2` satisfies `V ≥_E U ≥_E A` and `V ≥_E B`.

## Consequences

- **The gate.** For each `m`, the Ore half of `edge-split-operad-satisfies-ore` is
  exactly (Sync_m) plus (TD).
  - (Sync_m) is bh-free-61's pointwise, Serret-type statement. It is now proved for every
    `m` (lane proof, `unimodular-cells-synchronize-under-edge-splits-proof`, via
    `half-tube-lattice-points-are-edge-split-vertices`). So for each `m` the Ore half is
    exactly (TD).
  - (TD) is combinatorial; see `edge-split-descendant-dissections-are-tree-dominated`.
- **No Matui.** With saturation, `Mod(S_g) ≤ 𝒯_m = G_E` directly, and the
  derived-full-group step of `closed-mcg-bh-via-edge-split-operad` is no longer needed.
- **Evidence (MSI, single core, about five minutes in total).** No reversing failure
  was found. All numbers are in
  `research/artifacts/gq-bh-free-54-edge-split-reversing-tests.md`.
  - **(Ore_atom) on path trees.** The path tree of each of the 5043 descendants of `Δ`
    with entry sum at most 14 (24 of them not inherited by their children) was paired
    with each of the three atoms: 15129 of 15129 pairs have an upper bound.
  - **(TD).** All four prime dissections of the full operad recorded so far are
    dominated: `Z` by 7 pieces, `M` and `M′` by 10, and the 9-piece prime by 42. All
    their pieces are descendants of `Δ`. Of 17 random non-tree descendant
    dissections, 17 are dominated.
  - **(Ore).** Among random pairs of path trees, 386 have an upper bound and 14 hit
    the budget. Among random pairs of split trees with 3 to 40 pieces, 414 have an
    upper bound and 26 hit the size cap of 400 pieces.

## Lesson for general BH

For every refinement host of a higher-rank lattice, the calculus of fractions splits
into two independent statements.
- **Pointwise dynamics.** Do two runs of the free-choice continued-fraction algorithm
  through a point meet (Sync)? This is where Diophantine input lives.
- **Combinatorics.** Can the cells that all runs produce be organized into one run
  (TD)? This is a finite-type question about trees and involves no dynamics.

The false shortcut (LD_atom) tried to get the second for free from geometry.
Saturation, "the moves generate the whole full group", is the same pair of
statements. So one proof gives both finite presentation inputs and the embedding of
every subgroup of the full group.
