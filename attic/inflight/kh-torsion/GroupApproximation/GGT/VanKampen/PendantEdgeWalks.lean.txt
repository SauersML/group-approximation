import GroupApproximation.GGT.VanKampen.PendantEdgeMap
import GroupApproximation.GGT.VanKampen.CombMapSubdivisionBoundary
import GroupApproximation.Meta.AxiomGuard

/-!
# Face walks after attaching a pendant edge

Every old face traversal expands to a traversal of the map with a pendant edge
attached before `b`: each old dart stays in place, except that `b` is preceded
by the two new darts, out and back (`expand`).  The face equivalence
`faceEquiv` identifies the new faces with the old ones, and `allBoundary`
builds every new face boundary from the old boundaries.
-/

namespace GroupApproximation.GGT.VanKampen.PendantEdge

open Equiv PermOrbitInsert

universe u

variable (M : CombMap.{u}) (b : M.Dart)

noncomputable local instance : DecidableEq M.Dart := Classical.decEq _

theorem step_some_none : (toCombMap M b).facePerm (some none) = none := by
  rw [facePerm_apply, insertBefore_some, insertBefore_none, if_pos rfl]

theorem step_none : (toCombMap M b).facePerm none = some (some b) := by
  rw [facePerm_apply, insertBefore_none]

/-- Face rotation on the old darts: the successor `b` is replaced by the new
dart leaving the corner. -/
theorem step_embed (d : M.Dart) :
    (toCombMap M b).facePerm (some (some d)) =
      if M.facePerm d = b then some none else some (some (M.facePerm d)) := by
  rw [facePerm_apply, insertBefore_some, insertBefore_some]
  by_cases h : M.facePerm d = b
  · rw [if_pos h, if_neg (fun h' : (none : Option M.Dart) = some b => by cases h'), if_pos h]
  · rw [if_neg h, if_neg (fun h' => h (Option.some.inj h')), if_neg h]

/-- The walk replacing an old dart along its face. -/
noncomputable def expand (d : M.Dart) : List (EdgeInsertion.Dart M) :=
  if d = b then [some none, none, some (some d)] else [some (some d)]

theorem expand_nonempty (d : M.Dart) : expand M b d ≠ [] := by
  unfold expand
  split_ifs <;> exact List.cons_ne_nil _ _

theorem expand_head (d : M.Dart) :
    (expand M b d).head (expand_nonempty M b d) =
      if d = b then some none else some (some d) := by
  unfold expand
  split_ifs <;> rfl

theorem expand_last (d : M.Dart) :
    (expand M b d).getLast (expand_nonempty M b d) = some (some d) := by
  unfold expand
  split_ifs <;> rfl

theorem expand_chain (d : M.Dart) :
    (expand M b d).IsChain
      (fun x y : EdgeInsertion.Dart M => (toCombMap M b).facePerm x = y) := by
  unfold expand
  split_ifs with h
  · rw [h]
    exact List.isChain_cons_cons.mpr ⟨step_some_none M b, List.isChain_pair.mpr (step_none M b)⟩
  · exact List.isChain_singleton _

theorem expand_join (d : M.Dart) :
    (toCombMap M b).facePerm ((expand M b d).getLast (expand_nonempty M b d)) =
      (expand M b (M.facePerm d)).head (expand_nonempty M b _) := by
  rw [expand_last, expand_head, step_embed]

theorem origin_mem_expand (d : M.Dart) (x : EdgeInsertion.Dart M) (hx : x ∈ expand M b d) :
    oldRoot M b x = d := by
  unfold expand at hx
  split_ifs at hx with h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact h.symm
    · exact h.symm
    · rfl
  · simp only [List.mem_singleton] at hx
    rw [hx]
    rfl

theorem expand_nodup (d : M.Dart) : (expand M b d).Nodup := by
  unfold expand
  split_ifs <;> simp

theorem expanded_nodup (l : List M.Dart) (hl : l.Nodup) : (l.flatMap (expand M b)).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun d _ => expand_nodup M b d, ?_⟩
  apply hl.imp
  intro d e hde
  change List.Disjoint (expand M b d) (expand M b e)
  apply List.disjoint_left.mpr
  intro x hxd hxe
  exact hde ((origin_mem_expand M b d x hxd).symm.trans (origin_mem_expand M b e x hxe))

/-- **New faces are old faces.** -/
noncomputable def faceEquiv : (toCombMap M b).Face ≃ M.Face :=
  (EdgeSubdivision.orbitEquivOfEq (facePerm_eq M b)).trans
    ((PermOrbitInsert.orbitEquiv (insertBefore M.facePerm b) (some b)).trans
      (PermOrbitInsert.orbitEquiv M.facePerm b))

theorem faceEquiv_origin (x : EdgeInsertion.Dart M) :
    faceEquiv M b ((toCombMap M b).faceOf x) = M.faceOf (oldRoot M b x) := by
  rcases x with _ | (_ | d)
  all_goals
    simp only [faceEquiv, Equiv.trans_apply, CombMap.faceOf, EdgeSubdivision.orbitEquivOfEq_mk]
    rfl

variable (g : (toCombMap M b).Face) (B : FaceBoundary M (faceEquiv M b g))

theorem expanded_boundary_head :
    (toCombMap M b).faceOf
      ((B.darts.flatMap (expand M b)).head
        (CyclicListExpansion.nonempty (expand M b) (expand_nonempty M b) B.darts B.nonempty)) =
      g := by
  apply (faceEquiv M b).injective
  rw [faceEquiv_origin M b,
    CyclicListExpansion.head (expand M b) (expand_nonempty M b) B.darts B.nonempty,
    origin_mem_expand M b _ _ (List.head_mem (expand_nonempty M b _))]
  exact (B.mem_iff _).mp (List.head_mem B.nonempty)

theorem expanded_boundary_chain :
    (B.darts.flatMap (expand M b)).IsChain
      (fun x y : EdgeInsertion.Dart M => (toCombMap M b).facePerm x = y) :=
  CyclicListExpansion.chain (expand M b) (expand_nonempty M b) M.facePerm
    (toCombMap M b).facePerm (expand_chain M b) (expand_join M b) B.darts B.chain

theorem expanded_boundary_closes :
    (toCombMap M b).facePerm
      ((B.darts.flatMap (expand M b)).getLast
        (CyclicListExpansion.nonempty (expand M b) (expand_nonempty M b) B.darts B.nonempty)) =
      (B.darts.flatMap (expand M b)).head
        (CyclicListExpansion.nonempty (expand M b) (expand_nonempty M b) B.darts B.nonempty) :=
  CyclicListExpansion.closes (expand M b) (expand_nonempty M b) M.facePerm
    (toCombMap M b).facePerm (expand_join M b) B.darts B.nonempty B.closes

theorem expanded_boundary_mem (x : EdgeInsertion.Dart M) :
    x ∈ B.darts.flatMap (expand M b) ↔ (toCombMap M b).faceOf x = g := by
  let C := FaceBoundary.ofCyclicList (toCombMap M b) (B.darts.flatMap (expand M b))
    (CyclicListExpansion.nonempty (expand M b) (expand_nonempty M b) B.darts B.nonempty)
    (expanded_nodup M b B.darts B.nodup)
    (expanded_boundary_chain M b g B) (expanded_boundary_closes M b g B)
  have h := C.mem_iff x
  exact h.trans ⟨fun hd => hd.trans (expanded_boundary_head M b g B),
    fun hd => hd.trans (expanded_boundary_head M b g B).symm⟩

/-- A new face boundary, expanded from the corresponding old one. -/
noncomputable def boundary : FaceBoundary (toCombMap M b) g where
  darts := B.darts.flatMap (expand M b)
  nonempty := CyclicListExpansion.nonempty (expand M b) (expand_nonempty M b) B.darts B.nonempty
  nodup := expanded_nodup M b B.darts B.nodup
  mem_iff := expanded_boundary_mem M b g B
  chain := expanded_boundary_chain M b g B
  closes := expanded_boundary_closes M b g B
  length_eq_degree := Surgery.MapCollapse.length_eq_faceDegree_of_nodup (toCombMap M b) g
    (B.darts.flatMap (expand M b)) (expanded_nodup M b B.darts B.nodup)
    (expanded_boundary_mem M b g B)

/-- **All new face boundaries.** -/
noncomputable def allBoundary (FB : ∀ f : M.Face, FaceBoundary M f)
    (g : (toCombMap M b).Face) : FaceBoundary (toCombMap M b) g :=
  boundary M b g (FB (faceEquiv M b g))

theorem allBoundary_darts (FB : ∀ f : M.Face, FaceBoundary M f) (f : M.Face) :
    (allBoundary M b FB ((faceEquiv M b).symm f)).darts = (FB f).darts.flatMap (expand M b) := by
  change (FB (faceEquiv M b ((faceEquiv M b).symm f))).darts.flatMap (expand M b) = _
  exact congrArg (fun f : M.Face => (FB f).darts.flatMap (expand M b))
    ((faceEquiv M b).apply_symm_apply f)

end GroupApproximation.GGT.VanKampen.PendantEdge

#audit_axioms GroupApproximation.GGT.VanKampen.PendantEdge.step_embed
#audit_axioms GroupApproximation.GGT.VanKampen.PendantEdge.expand_join
#audit_axioms GroupApproximation.GGT.VanKampen.PendantEdge.expanded_nodup
#audit_axioms GroupApproximation.GGT.VanKampen.PendantEdge.faceEquiv_origin
#audit_axioms GroupApproximation.GGT.VanKampen.PendantEdge.boundary
#audit_axioms GroupApproximation.GGT.VanKampen.PendantEdge.allBoundary_darts
