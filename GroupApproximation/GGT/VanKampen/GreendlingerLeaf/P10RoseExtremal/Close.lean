import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEndpoint.SingleRegion
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseKeptBalance.Balance
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.Balance
import GroupApproximation.Meta.AxiomGuard

/-!
# A chained re-listing of the kept darts of a region move closes up

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-08, part 1.

Let `c` be a duplicate-free list of exactly the boundary darts of a face set, `z` a colouring that
is constant along `FaceClassStep M (walkKeep M c)` and never colours both sides of a dart of `c`,
and `L` a re-listing (`List.Perm`) of the kept darts `c.filter (movePred M z)`.  If `L` is
nonempty and each dart of `L` ends where the next one starts, then `L` is a closed dart walk: the
last dart ends where the first one starts.

## Route

* `filter_movePred_countP_balanced`: the kept darts are the boundary darts of the flipped face set
  `flipFaces M faces z` (`P10Rose.FilterMove.isBoundaryDart_flipFaces_iff`, module
  `P10Rose/Live/Move`), duplicate-free as a filter of `c`, so they are balanced at every vertex
  (`P10RoseKeptBalance.boundaryCountPBalanced`).
* `isClosedDartWalk_of_perm_filter`: balance passes to the re-listing `L` (`List.Perm.countP_eq`).
  Along the chain `L`, at the vertex `x` where `L` starts,
  `#starts + [last ends at x] = #ends + [first starts at x] = #ends + 1`
  (`P10RoseEuler.chain_countP`); with `#starts = #ends` the last dart ends at `x`.

The live move API is reached through `P10RoseEndpoint/SingleRegion` (which imports
`P10Rose/Live/Reduction`); the dead filter route (`P10Rose/FilterMove`, `P10RoseKeptBalance/Kept`)
is not imported.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremal

universe v

/-- **The kept darts of a region move are balanced at every vertex.** -/
theorem filter_movePred_countP_balanced {M : CombMap.{v}} [DecidableEq M.Vertex]
    {faces : Finset M.Face} {c : List M.Dart} (hnodup : c.Nodup)
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d) {z : M.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep M (SimpleClosedWalkSides.walkKeep M c) x y → z x = z y)
    (hind : ∀ d ∈ c, z d = false ∨ z (M.alpha d) = false) (x : M.Vertex) :
    (c.filter (P10Rose.FilterMove.movePred M z)).countP (fun d => decide (M.vertexOf d = x)) =
      (c.filter (P10Rose.FilterMove.movePred M z)).countP
        (fun d => decide (M.vertexOf (M.alpha d) = x)) :=
  P10RoseKeptBalance.boundaryCountPBalanced M (P10Rose.FilterMove.flipFaces M faces z)
    (c.filter (P10Rose.FilterMove.movePred M z)) (hnodup.filter _)
    (fun d => List.mem_filter.trans
      (P10Rose.FilterMove.isBoundaryDart_flipFaces_iff hc hz hind d).symm) x

/-- **A chained re-listing of the kept darts is a closed dart walk.**  The closing equation of
`IsClosedDartWalk` follows from the balance of the kept darts and the count along a chain. -/
theorem isClosedDartWalk_of_perm_filter {M : CombMap.{v}} {faces : Finset M.Face}
    {c : List M.Dart} (hnodup : c.Nodup)
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d) {z : M.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep M (SimpleClosedWalkSides.walkKeep M c) x y → z x = z y)
    (hind : ∀ d ∈ c, z d = false ∨ z (M.alpha d) = false) {L : List M.Dart}
    (hperm : List.Perm L (c.filter (P10Rose.FilterMove.movePred M z))) (hne : L ≠ [])
    (hchain : L.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)) :
    IsClosedDartWalk M L := by
  classical
  refine ⟨hne, hchain, ?_⟩
  have hbal := filter_movePred_countP_balanced hnodup hc hz hind (M.vertexOf (L.head hne))
  have hbal' : L.countP (fun d => decide (M.vertexOf d = M.vertexOf (L.head hne))) =
      L.countP (fun d => decide (M.vertexOf (M.alpha d) = M.vertexOf (L.head hne))) :=
    (hperm.countP_eq _).trans (hbal.trans (hperm.countP_eq _).symm)
  have hcount : L.countP (fun d => decide (M.vertexOf d = M.vertexOf (L.head hne))) +
      [L.getLast hne].countP
        (fun d => decide (M.vertexOf (M.alpha d) = M.vertexOf (L.head hne))) =
      L.countP (fun d => decide (M.vertexOf (M.alpha d) = M.vertexOf (L.head hne))) +
        [L.head hne].countP (fun d => decide (M.vertexOf d = M.vertexOf (L.head hne))) :=
    P10RoseEuler.chain_countP (s := M.vertexOf) (t := fun d => M.vertexOf (M.alpha d))
      (M.vertexOf (L.head hne)) hne hchain
  have hhead :
      [L.head hne].countP (fun d => decide (M.vertexOf d = M.vertexOf (L.head hne))) = 1 := by
    simp
  by_contra hlast
  have h0 : [L.getLast hne].countP
      (fun d => decide (M.vertexOf (M.alpha d) = M.vertexOf (L.head hne))) = 0 := by
    simp [hlast]
  omega

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremal

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremal.filter_movePred_countP_balanced
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremal.isClosedDartWalk_of_perm_filter
