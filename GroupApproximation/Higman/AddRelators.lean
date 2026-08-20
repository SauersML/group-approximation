import GroupApproximation.Higman.RelabelPresentation

/-!
# Adding relators is taking a union

Every construction in the assembly of input (4) is "a presented group, modulo
some more relations": the HNN extension is the free product of its base with
`ℤ` modulo the stable-letter relations, and the free product itself is a
presented group by `Algebra.CoprodIPresentation`.  To keep the whole thing
inside `PresentedGroup` --- which is what `Higman.RelatorRE` consumes --- one
needs the obvious but unrecorded fact that imposing further relators on a
presented group gives the presented group of the larger relator set.

    PresentedGroup (S ∪ T)  ≃*  PresentedGroup S ⧸ ⟪image of T⟫ .

The proof is the third isomorphism theorem together with
`Subgroup.normalClosure_union`, and the one thing to check is that the image of
`⟪S⟫ ⊔ ⟪T⟫` in `PresentedGroup S` is the normal closure of the image of `T` ---
which it is, because `⟪S⟫` dies and `Subgroup.map_normalClosure` moves the
normal closure across the surjection.

With this, a construction's relator set is literally the union of the pieces'
relator sets, and `Higman.search_union`, `Higman.search_image` and
`Higman.mem_range_iff_search` show the union stays enumerable.
-/

namespace GroupApproximation
namespace Higman

variable {α : Type}

/-- The image of the enlarged normal closure is the normal closure of the
image. -/
theorem map_normalClosure_union (S T : Set (FreeGroup α)) :
    (Subgroup.normalClosure (S ∪ T)).map
        (QuotientGroup.mk' (Subgroup.normalClosure S))
      = Subgroup.normalClosure
          ((QuotientGroup.mk' (Subgroup.normalClosure S)) '' T) := by
  rw [Subgroup.normalClosure_union, Subgroup.map_sup]
  have hbot : (Subgroup.normalClosure S).map
      (QuotientGroup.mk' (Subgroup.normalClosure S)) = ⊥ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change (QuotientGroup.mk' (Subgroup.normalClosure S)) x = 1
      exact (QuotientGroup.eq_one_iff x).2 hx
    · exact bot_le
  rw [hbot, bot_sup_eq]
  exact Subgroup.map_normalClosure T _ (QuotientGroup.mk'_surjective _)

/-- **Adding relators is taking a union.** -/
noncomputable def presentedGroupUnionEquiv (S T : Set (FreeGroup α)) :
    PresentedGroup (S ∪ T) ≃*
      (PresentedGroup S) ⧸
        Subgroup.normalClosure
          ((QuotientGroup.mk' (Subgroup.normalClosure S)) '' T) := by
  refine MulEquiv.symm ?_
  let N : Subgroup (FreeGroup α) := Subgroup.normalClosure S
  let M : Subgroup (FreeGroup α) := Subgroup.normalClosure (S ∪ T)
  let q : FreeGroup α →* FreeGroup α ⧸ N := QuotientGroup.mk' N
  let P : Subgroup (FreeGroup α ⧸ N) := Subgroup.normalClosure (q '' T)
  let Q : Subgroup (FreeGroup α ⧸ N) := M.map q
  haveI : N.Normal := by dsimp [N]; infer_instance
  haveI : M.Normal := by dsimp [M]; infer_instance
  haveI : P.Normal := by dsimp [P]; infer_instance
  haveI : Q.Normal := by dsimp [Q, q]; infer_instance
  have hNM : N ≤ M := by
    dsimp [N, M]
    exact Subgroup.normalClosure_le_normal
      (Set.Subset.trans Set.subset_union_left Subgroup.subset_normalClosure)
  have hQP : Q = P := by
    simpa only [N, M, q, Q, P] using map_normalClosure_union S T
  change (FreeGroup α ⧸ N) ⧸ P ≃* FreeGroup α ⧸ M
  exact (QuotientGroup.quotientMulEquivOfEq hQP.symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient N M hNM)

end Higman
end GroupApproximation
