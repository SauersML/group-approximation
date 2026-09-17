import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseKeptBalance.Balance
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove
import GroupApproximation.Meta.AxiomGuard

/-!
# The kept darts of a region move are balanced

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  In the single-region move of the rose step (lane `gl-p10-08`), the new
boundary `s_1 t_1^{-1} s_2 t_2` is obtained by re-listing the kept darts `c.filter (movePred z)` of
the old boundary cycle `c` as a closed walk (Euler, lane `gl-p10-06`).  This module supplies the
balance hypothesis of that re-listing.

## Statement (`filter_movePred_balanced`)

Let `c` be a duplicate-free list of exactly the boundary darts of a face set `F`, and let
`z : Dart → Bool` be a move: constant along the face-class steps `FaceClassStep M (walkKeep M c)`
and never flipping both sides of a dart of `c`.  Then for every vertex `x`, the kept darts
`c.filter (FilterMove.movePred M z)` contain as many darts starting at `x` as darts ending at `x`.

## Proof

By `FilterMove.isBoundaryDart_flipFaces_iff`, the boundary darts of the moved face set
`FilterMove.flipFaces M F z` are exactly the members of `c` with `movePred M z = true`, that is, the
members of `c.filter (movePred M z)` (`List.mem_filter`).  This filter is duplicate-free
(`List.Nodup.filter`).  So the kept darts form a duplicate-free list of exactly the boundary darts
of a face set, and the balance of boundary cycles (`BoundaryCountPBalancedStatement`, module
`Balance`) applies.

* `filter_movePred_balanced_of_boundaryCountPBalanced`: the reduction to the list form of lane
  `gl-p10-05`, stated as `BoundaryCountPBalancedStatement` (not on disk when this lane was
  authored).
* `filter_movePred_balanced`: the unconditional endpoint, using `boundaryCountPBalanced`.

The endpoint takes an arbitrary `DecidableEq M.Vertex` instance (the lane's signature leaves the
instance implicit; with `open Classical` it is the classical instance, which is covered).

## Import note for the checker

The flip-move API (`FilterMove.movePred`, `FilterMove.flipFaces`,
`FilterMove.isBoundaryDart_flipFaces_iff`) is imported from `P10Rose/FilterMove`, where it exists
on disk.  Lane `gl-p10-01` re-creates it with identical names in `P10Rose/Live/Move`; when that
lands and `P10Rose/FilterMove` is deleted, repoint the second import of this module to
`GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Live.Move` (one line, no other change).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseKeptBalance

universe v

/-- **Kept darts of a move, reduced to boundary balance**: the kept darts are the boundary darts of
the moved face set, so the list form of boundary balance applies to them. -/
theorem filter_movePred_balanced_of_boundaryCountPBalanced
    (hbal : BoundaryCountPBalancedStatement.{v}) {M : CombMap.{v}} [DecidableEq M.Vertex]
    {F : Finset M.Face} {c : List M.Dart} (hnodup : c.Nodup)
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d) {z : M.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep M (SimpleClosedWalkSides.walkKeep M c) x y → z x = z y)
    (hind : ∀ d ∈ c, z d = false ∨ z (M.alpha d) = false) (x : M.Vertex) :
    (c.filter (P10Rose.FilterMove.movePred M z)).countP (fun d => decide (M.vertexOf d = x)) =
      (c.filter (P10Rose.FilterMove.movePred M z)).countP
        (fun d => decide (M.vertexOf (M.alpha d) = x)) :=
  hbal M (P10Rose.FilterMove.flipFaces M F z) (c.filter (P10Rose.FilterMove.movePred M z))
    (hnodup.filter _)
    (fun d => List.mem_filter.trans
      (P10Rose.FilterMove.isBoundaryDart_flipFaces_iff hc hz hind d).symm) x

/-- **The kept darts of a region move are balanced at every vertex** (lane `gl-p10-07`). -/
theorem filter_movePred_balanced {M : CombMap.{v}} [DecidableEq M.Vertex]
    {F : Finset M.Face} {c : List M.Dart} (hnodup : c.Nodup)
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d) {z : M.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep M (SimpleClosedWalkSides.walkKeep M c) x y → z x = z y)
    (hind : ∀ d ∈ c, z d = false ∨ z (M.alpha d) = false) (x : M.Vertex) :
    (c.filter (P10Rose.FilterMove.movePred M z)).countP (fun d => decide (M.vertexOf d = x)) =
      (c.filter (P10Rose.FilterMove.movePred M z)).countP
        (fun d => decide (M.vertexOf (M.alpha d) = x)) :=
  filter_movePred_balanced_of_boundaryCountPBalanced boundaryCountPBalanced hnodup hc hz hind x

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseKeptBalance

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseKeptBalance.filter_movePred_balanced_of_boundaryCountPBalanced
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseKeptBalance.filter_movePred_balanced
