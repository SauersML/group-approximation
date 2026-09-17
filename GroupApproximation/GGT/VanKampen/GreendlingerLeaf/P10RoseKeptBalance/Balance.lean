import GroupApproximation.GGT.VanKampen.FaceSetBoundaryCircuits
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionUnpinched
import GroupApproximation.Meta.AxiomGuard

/-!
# The boundary darts of a face set are balanced at every vertex

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Before a re-listing of kept darts can be a closed walk, the kept darts
must enter and leave every vertex equally often.  This module proves that for the boundary darts
of any face set, in the list form used by lane `gl-p10-07`.

## Statement (`BoundaryCountPBalancedStatement`)

Let `M` be a combinatorial map, `F` a finite set of faces and `c` a duplicate-free list whose
members are exactly the boundary darts of `F`.  For every vertex `x`, the number of darts of `c`
starting at `x` (`vertexOf d = x`) equals the number of darts of `c` ending at `x`
(`vertexOf (alpha d) = x`).

This is the upstream interface of lane `gl-p10-05` (list form of `boundary_balanced`), which is
being authored in parallel and is not on disk; it is stated here as a `Prop` with the reduction
`P10RoseKeptBalance.filter_movePred_balanced_of_boundaryCountPBalanced` (module `Kept`), and also
closed here (`boundaryCountPBalanced`), so that the endpoint of this lane is unconditional.  The
statement takes an arbitrary `DecidableEq M.Vertex` instance, so it covers the classical one.

## Proof

`Surgery.MapCollapse.FaceSetCircuits.boundaryPerm M F` is a permutation of the boundary darts, and
`boundaryPerm_walk` says that the boundary walk from `d` reaches `boundaryPerm d`.  A boundary walk
first advances around the face (`facePerm d = sigma (alpha d)`) and then only rotates with `sigma`,
so `vertexOf (boundaryPerm d) = vertexOf (alpha d)`
(`Surgery.MapCollapse.vertexOf_eq_of_boundaryWalk`).  Hence `d ↦ boundaryPerm d` maps the boundary
darts ending at `x` injectively onto the boundary darts starting at `x` (surjectivity by
`boundaryPerm.symm`).  Counting in the list: `countP p c = #(c.filter p).toFinset` because `c` is
duplicate-free (`List.toFinset_card_of_nodup`), and `Finset.card_bij` compares the two finsets.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseKeptBalance

universe v

/-- **Balance of a boundary cycle** (interface of lane `gl-p10-05`, list form): a duplicate-free
list of exactly the boundary darts of a face set has as many darts starting at each vertex as
darts ending there. -/
def BoundaryCountPBalancedStatement : Prop :=
  ∀ (M : CombMap.{v}) [DecidableEq M.Vertex] (F : Finset M.Face) (c : List M.Dart),
    c.Nodup → (∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d) → ∀ x : M.Vertex,
      c.countP (fun d => decide (M.vertexOf d = x)) =
        c.countP (fun d => decide (M.vertexOf (M.alpha d) = x))

/-- **The boundary darts of a face set are balanced at every vertex**: the boundary successor
`FaceSetCircuits.boundaryPerm` matches the darts ending at a vertex with those starting there. -/
theorem boundaryCountPBalanced : BoundaryCountPBalancedStatement.{v} := by
  intro M _ F c hnodup hc x
  classical
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (hnodup.filter _),
    ← List.toFinset_card_of_nodup (hnodup.filter _)]
  symm
  refine Finset.card_bij
    (fun d hd => (Surgery.MapCollapse.FaceSetCircuits.boundaryPerm M F
      ⟨d, (hc d).mp (List.mem_filter.mp (List.mem_toFinset.mp hd)).1⟩).1) ?_ ?_ ?_
  · intro a ha
    have ha' := List.mem_filter.mp (List.mem_toFinset.mp ha)
    have hb := Surgery.MapCollapse.FaceSetCircuits.boundaryPerm_walk M F ⟨a, (hc a).mp ha'.1⟩
    refine List.mem_toFinset.mpr (List.mem_filter.mpr
      ⟨(hc _).mpr (Surgery.MapCollapse.FaceSetCircuits.boundaryPerm M F
        ⟨a, (hc a).mp ha'.1⟩).2, ?_⟩)
    exact decide_eq_true
      ((Surgery.MapCollapse.vertexOf_eq_of_boundaryWalk hb).trans (of_decide_eq_true ha'.2))
  · intro a₁ _ a₂ _ h
    exact congrArg Subtype.val
      ((Surgery.MapCollapse.FaceSetCircuits.boundaryPerm M F).injective (Subtype.ext h))
  · intro b hb
    have hb' := List.mem_filter.mp (List.mem_toFinset.mp hb)
    have hbd : Surgery.MapCollapse.IsBoundaryDart M F b := (hc b).mp hb'.1
    have hwalk := Surgery.MapCollapse.vertexOf_eq_of_boundaryWalk
      (Surgery.MapCollapse.FaceSetCircuits.boundaryPerm_walk M F
        ((Surgery.MapCollapse.FaceSetCircuits.boundaryPerm M F).symm ⟨b, hbd⟩))
    rw [Equiv.apply_symm_apply] at hwalk
    refine ⟨((Surgery.MapCollapse.FaceSetCircuits.boundaryPerm M F).symm ⟨b, hbd⟩).1,
      List.mem_toFinset.mpr (List.mem_filter.mpr
        ⟨(hc _).mpr ((Surgery.MapCollapse.FaceSetCircuits.boundaryPerm M F).symm ⟨b, hbd⟩).2,
          decide_eq_true (hwalk.symm.trans (of_decide_eq_true hb'.2))⟩), ?_⟩
    exact congrArg Subtype.val
      (Equiv.apply_symm_apply (Surgery.MapCollapse.FaceSetCircuits.boundaryPerm M F) ⟨b, hbd⟩)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseKeptBalance

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseKeptBalance.BoundaryCountPBalancedStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseKeptBalance.boundaryCountPBalanced
