import GroupApproximation.GGT.VanKampen.CombMapSubdivisionWalks

/-! # Every actual face boundary after subdivision -/

namespace GroupApproximation.GGT.VanKampen.EdgeSubdivision

universe u
variable (M : CombMap.{u}) (a : M.Dart)

theorem faceEquiv_origin (d : Dart M) :
    faceEquiv M a ((toCombMap M a).faceOf d) = M.faceOf (origin M a d) := by
  rcases d with _ | (_ | d)
  · exact faceEquiv_none M a
  · exact faceEquiv_positive M a
  · exact faceEquiv_embed M a d

variable (g : (toCombMap M a).Face) (B : FaceBoundary M (faceEquiv M a g))

theorem expanded_boundary_head :
    (toCombMap M a).faceOf
      ((B.darts.flatMap (expand M a)).head
        (CyclicListExpansion.nonempty (expand M a) (expand_nonempty M a) B.darts B.nonempty)) = g := by
  apply (faceEquiv M a).injective
  rw [faceEquiv_origin M a]
  rw [CyclicListExpansion.head (expand M a) (expand_nonempty M a) B.darts B.nonempty]
  rw [origin_mem_expand M a _ _ (List.head_mem (expand_nonempty M a _))]
  exact (B.mem_iff _).mp (List.head_mem B.nonempty)

theorem expanded_boundary_chain :
    (B.darts.flatMap (expand M a)).IsChain
      (fun d e : Dart M => (toCombMap M a).facePerm d = e) :=
  CyclicListExpansion.chain (expand M a) (expand_nonempty M a) M.facePerm
    (toCombMap M a).facePerm (expand_chain M a) (expand_join M a) B.darts B.chain

theorem expanded_boundary_closes :
    (toCombMap M a).facePerm
      ((B.darts.flatMap (expand M a)).getLast
        (CyclicListExpansion.nonempty (expand M a) (expand_nonempty M a) B.darts B.nonempty)) =
      (B.darts.flatMap (expand M a)).head
        (CyclicListExpansion.nonempty (expand M a) (expand_nonempty M a) B.darts B.nonempty) :=
  CyclicListExpansion.closes (expand M a) (expand_nonempty M a) M.facePerm
    (toCombMap M a).facePerm (expand_join M a) B.darts B.nonempty B.closes

theorem expanded_boundary_mem (d : Dart M) :
    d ∈ B.darts.flatMap (expand M a) ↔ (toCombMap M a).faceOf d = g := by
  let C := FaceBoundary.ofCyclicList (toCombMap M a) (B.darts.flatMap (expand M a))
    (CyclicListExpansion.nonempty (expand M a) (expand_nonempty M a) B.darts B.nonempty)
    (expanded_nodup M a B.darts B.nodup)
    (expanded_boundary_chain M a g B) (expanded_boundary_closes M a g B)
  have h := C.mem_iff d
  exact h.trans ⟨fun hd => hd.trans (expanded_boundary_head M a g B),
    fun hd => hd.trans (expanded_boundary_head M a g B).symm⟩

/-- The face index and degree are derived from the actual expanded cycle. -/
noncomputable def boundary : FaceBoundary (toCombMap M a) g where
  darts := B.darts.flatMap (expand M a)
  nonempty := CyclicListExpansion.nonempty (expand M a) (expand_nonempty M a) B.darts B.nonempty
  nodup := expanded_nodup M a B.darts B.nodup
  mem_iff := expanded_boundary_mem M a g B
  chain := expanded_boundary_chain M a g B
  closes := expanded_boundary_closes M a g B
  length_eq_degree := Surgery.MapCollapse.length_eq_faceDegree_of_nodup (toCombMap M a) g
    (B.darts.flatMap (expand M a)) (expanded_nodup M a B.darts B.nodup)
    (expanded_boundary_mem M a g B)

noncomputable def allBoundary (FB : ∀ f : M.Face, FaceBoundary M f)
    (g : (toCombMap M a).Face) : FaceBoundary (toCombMap M a) g :=
  boundary M a g (FB (faceEquiv M a g))

theorem allBoundary_darts (FB : ∀ f : M.Face, FaceBoundary M f) (f : M.Face) :
    (allBoundary M a FB ((faceEquiv M a).symm f)).darts = (FB f).darts.flatMap (expand M a) := by
  change (FB (faceEquiv M a ((faceEquiv M a).symm f))).darts.flatMap (expand M a) = _
  exact congrArg (fun f : M.Face => (FB f).darts.flatMap (expand M a))
    ((faceEquiv M a).apply_symm_apply f)

end GroupApproximation.GGT.VanKampen.EdgeSubdivision

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.boundary
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.allBoundary_darts
