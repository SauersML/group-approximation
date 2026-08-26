import GroupApproximation.Higman.PairedReturnCutter
import GroupApproximation.Sofic.ProfiniteRetract

/-!
# Profinite closedness of the synchronized right subgroup

The synchronized subgroup `Q` is the graph of the fold homomorphism over the
paired-return edge.  Its first projection is an isomorphism because
`muToM` is the range restriction defining the edge.  Consequently `Q` is a
retract of `Edge × Sync`, and hence is profinitely closed.
-/

namespace GroupApproximation
namespace Higman
namespace PairedReturnQProfinite

open PairedReturnCutter
open Conj

/-- The retraction killing `a`, with codomain restricted to `Sync = K`. -/
def retKSync : F₃ →* Sync :=
  FreeGroup.lift fun i : Fin 3 ↦
    if i = 0 then 1 else if i = 1 then bSync else cSync

@[simp] theorem retKSync_a : retKSync a = 1 := by
  simp [retKSync, a]

@[simp] theorem retKSync_b : retKSync b = bSync := by
  simp [retKSync, b]

@[simp] theorem retKSync_c : retKSync c = cSync := by
  simp [retKSync, c]

/-- Forgetting the restricted codomain recovers `Coord.retK`. -/
theorem subtype_comp_retKSync :
    (K.subtype).comp retKSync = Coord.retK := by
  apply FreeGroup.ext_hom
  intro i
  change ((retKSync (FreeGroup.of i) : Sync) : F₃) =
    Coord.retK (FreeGroup.of i)
  unfold retKSync Coord.retK
  rw [FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
  fin_cases i <;> simp [bSync, cSync, b, c]

/-- The fold map, read intrinsically on the paired-return edge. -/
def edgeFold : Edge →* Sync :=
  PairedReturnGraphIntersection.psi.codRestrict K fun e ↦ by
    change Coord.retK (e : PairedReturnGraphIntersection.P).1 ∈ K
    rw [← subtype_comp_retKSync]
    exact (retKSync (e : PairedReturnGraphIntersection.P).1).property

@[simp] theorem edgeFold_muToM (w : Monoid.Coprod Sync Sync) :
    edgeFold (PairedReturnGraphIntersection.muToM w) =
      PairedFoldKernel.fold Sync w := by
  apply Subtype.ext
  exact PairedReturnGraphIntersection.psi_mu w

/-- The graph embedding whose range is `Q`. -/
def qGraph : Edge →* C := (MonoidHom.id Edge).prod edgeFold

@[simp] theorem qGraph_apply (e : Edge) : qGraph e = (e, edgeFold e) := rfl

/-- The transition range is literally the graph of `edgeFold`. -/
theorem Q_eq_qGraph_range : Q = qGraph.range := by
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    refine ⟨PairedReturnGraphIntersection.muToM w, ?_⟩
    apply Prod.ext
    · rfl
    · exact edgeFold_muToM w
  · rintro z ⟨e, rfl⟩
    obtain ⟨w, hw⟩ :=
      PairedReturnGraphIntersection.mu.rangeRestrict_surjective e
    refine ⟨w, ?_⟩
    calc
      transition w = qGraph (PairedReturnGraphIntersection.muToM w) := by
        apply Prod.ext
        · rfl
        · exact (edgeFold_muToM w).symm
      _ = qGraph e := congrArg qGraph hw

/-- The graph embedding, with codomain restricted to `Q`. -/
def qGraphToQ : Edge →* Q :=
  qGraph.codRestrict Q fun e ↦ by
    rw [Q_eq_qGraph_range]
    exact ⟨e, rfl⟩

/-- Retraction from the right vertex group onto its synchronized graph. -/
def qRet : C →* Q := qGraphToQ.comp (MonoidHom.fst Edge Sync)

theorem qRet_comp_subtype :
    qRet.comp Q.subtype = MonoidHom.id Q := by
  apply MonoidHom.ext
  intro z
  have hz : (z : C) ∈ qGraph.range := by
    rw [← Q_eq_qGraph_range]
    exact z.property
  obtain ⟨e, he⟩ := hz
  apply Subtype.ext
  change qGraph (z : C).1 = (z : C)
  rw [← he]
  rfl

/-- **The synchronized right subgroup is profinitely closed.** -/
theorem profiniteClosure_Q : profiniteClosure Q = Q := by
  letI : Group.ResiduallyFinite Edge :=
    residuallyFinite_of_injective PairedReturnGraphIntersection.M.subtype
      Subtype.val_injective
  letI : Group.ResiduallyFinite Sync :=
    residuallyFinite_of_injective K.subtype Subtype.val_injective
  have h := profiniteClosure_range_eq_range_of_retraction
    Q.subtype qRet qRet_comp_subtype
  simpa using h

end PairedReturnQProfinite
end Higman
end GroupApproximation
