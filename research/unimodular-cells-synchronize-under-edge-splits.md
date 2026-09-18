---
rg: 2
id: unimodular-cells-synchronize-under-edge-splits
kind: claim
title: Every unimodular cell inside a unimodular cell is a finite union of cells that are edge-split descendants of both
distinct_from:
  edge-split-descendants-are-not-factor-closed: that shows a descendant of the simplex lying in a child need not descend from the child; this asks for the weaker, dissection-level statement that the two descendant systems always have a common refinement.
  edge-splits-cut-every-rational-hyperplane: that is cofinality of edge-split cells; this is synchronization, the second Stein–Farley input for the rational projective full groups.
  rational-projective-full-groups-are-finitely-presented: that is the finiteness gate; this is one precise combinatorial input to it, equivalent to directedness of the edge-split expansion poset.
---

**OPEN** (lane bh-free-61, 2026-09-18). Trivial for `m = 1`. For `m ≥ 2`,
checked by hand on the two witnesses of `edge-split-descendants-are-not-factor-closed`.

## Statement

**(Sync_m).** Let `c ⊆ C` be unimodular cells in `R^{m+1}`. Then `c` is a finite
union, up to walls, of cells that are edge-split descendants of both `c` and `C`.

## Equivalent forms

1. **Matrix game.**
   - By `GL_{m+1}(Z)`-invariance, take `C = Δ` and `c = cone(X)`, with `X`
     nonnegative and unimodular. `(Sync_m)` holds for `(c, C)` if the following
     game can be won from `X`.
   - **Positions.** Nonnegative unimodular matrices.
   - **Moves.** A *left reduction* `X ↦ X − E_{ab}X` (row `a` minus row `b`) is
     allowed when `row_a(X) ≥ row_b(X)`. A *right split* replaces `X` by the two
     positions `X T_{cd}` and `X T_{dc}`, both of which must then be won.
   - **Winning.** A position is won when it is a permutation matrix.

   A won game tree is a split tree of `c` whose leaves are cells in both
   descendant systems. The converse is not checked: a dissection of `c` into
   common descendants need not come from a split tree of `c`.
2. **Local form.** `(Sync_m)` holds for `(c, C)` if and only if every point of the
   clopen `c ⊆ Ŝ_m` lies in some common descendant.
   - Given a finite subcover, disjointify it with the cut lemma of
     `edge-splits-cut-every-rational-hyperplane`. Descendants of a common
     descendant are again common descendants.
3. **Directedness.** `(Sync_m)` for all pairs is equivalent to directedness of
   the poset whose elements are dissections of `Ŝ_m` into unimodular cells, where
   `D ≤ D'` means that every piece of `D'` descends from the piece of `D`
   containing it.
   - **(⇐)** Apply directedness to a dissection containing `C` and one
     containing `c`. Both exist by the basis part of the cut lemma.
   - **(⇒)** Given `D_1` and `D_2`, cut each piece of `D_1` by all facet
     hyperplanes of `D_2`. By the cut lemma, each resulting cell `p` is a
     descendant of its `D_1` piece and lies in a single piece `Q` of `D_2`. Then
     apply `(Sync_m)` to `p ⊆ Q`.

## Why it matters

Directedness of this poset is the second of the three Stein–Farley inputs for
`rational-projective-full-groups-are-finitely-presented` (see the lesson in
`edge-splits-cut-every-rational-hyperplane`). Its realization is then
contractible. With the labelled set-up of Attempt 1 of the gate node, only
descending-link connectivity and the Morse bookkeeping would remain.

For `m = 1` it is automatic. Every nonnegative `X ∈ GL_2(Z)` other than a
permutation has a row dominance, so left reductions alone win.

## Attempts

1. **A μ-induction** (lane bh-free-61, 2026-09-18; proposal, not carried out).
   - Let `μ(X)` be the least entry sum of a matrix reachable from `X` by left
     reductions. Left reductions strictly lower the entry sum, so this
     terminates.
   - `(Sync_m)` would follow by induction on `μ` from a **split lemma**: every
     *stuck* `X` (not a permutation, no row dominance) has a pair `(c, d)` such
     that both `μ(X T_{cd})` and `μ(X T_{dc})` are less than the entry sum of `X`.
   - **Evidence.** For `M = [[3,1,0],[1,1,1],[0,1,2]]`, the pair `(0,2)` gives
     `μ = 3` for both children, since both reach permutations.
   - **A necessary condition, for `m = 2`.** Every incomparable pair of rows
     has a direction `(a,b)` with exactly one column `d` where
     `X[a,d] < X[b,d]`. The child `X T_{cd}` gains the dominance `(a,b)` exactly
     when `X[a,c] − X[b,c] ≥ X[b,d] − X[a,d]`. So the split lemma asks for two
     such near-dominances whose deficit columns `c ≠ d` are each covered by the
     surplus in the other's column.
   - **The one-step split lemma is false** (same lane, same day). For
     `X = [[9,2,0],[2,1,1],[0,1,2]]` (determinant 1, stuck), every split has a
     stuck child:
     - `(0,1)`: both children are stuck;
     - `(1,2)`: the child replacing the second ray is stuck;
     - `(0,2)`: the child replacing the first ray is stuck.
     A stuck child has `μ` equal to its entry sum, which exceeds that of `X`.
     So the induction needs a multi-level potential.
2. **Braid-cut strategy** (lane bh-free-61, 2026-09-18; evidence only).
   - **The strategy.** Pick a braid form `ℓ = x_a − x_b` of the current `Δ`-side
     cell. Its coefficient vector on `c` is `row_a − row_b`. Run the Euclid rule of
     the cut lemma on that vector. Every leaf then has the dominance `(a,b)` or
     `(b,a)`. Left-reduce greedily and repeat.
   - **It wins both hand examples.**
     - `M`: one split.
     - `X = [[9,2,0],[2,1,1],[0,1,2]]` with `ℓ = x_1 − x_2`: split `(0,2)`, then
       split `(0,2)` again in the child replacing the first ray. All three leaves
       reduce to permutation matrices. The leaves are
       `[[9,2,9],[2,1,3],[0,1,2]]`, `[[9,2,0],[4,1,1],[4,1,2]]` and
       `[[9,2,9],[3,1,4],[2,1,4]]`.
   - **Status.** No termination measure is known. A bounded exact search over
     stuck `3×3` matrices of small entry sum would test the strategy. Planted
     positives: `M` and `X`.

## Lesson for general BH

Synchronization for boundary actions of higher-rank lattices is a
Serret-type statement about a free-choice multidimensional continued fraction.
- In rank one it is Serret's theorem: `GL_2(Z)`-equivalent irrationals have
  equal continued-fraction tails.
- In higher rank the algorithm may choose freely at every step, and that freedom
  is what makes `(Sync_m)` plausible.
- For hosts built from a lattice acting on a rational Cantorization, this
  free-choice Serret statement is the directedness input of the natural
  Stein–Farley complex. A proof of `(Sync_m)` would transfer to every such host
  whose cells are unimodular simplices.
