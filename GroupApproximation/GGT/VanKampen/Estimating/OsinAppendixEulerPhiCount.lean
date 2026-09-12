import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhi
import GroupApproximation.Meta.AxiomGuard

/-!
# Counting darts and vertices of `Φ_M`

For the subdivided graph `phiMap family E` of `GGT/VanKampen/Estimating/OsinAppendixEulerPhi.lean`:

* every retained dart is one of the four crossing darts of one region, so there are `4|E|` darts
  (`phiMap_dartCount`);
* a vertex is either a cell, read off any cell dart at it, or a region's midpoint, so for a cell set
  `V` containing all ends of the regions there are at most `|V| + |E|` vertices
  (`phiMap_vertexCount_le`).
-/

namespace GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

open Equiv
universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {family E : Finset (RegionCandidate D eps Delta)}

/-- **`Φ_M` subdivided has four darts per region.** -/
theorem phiMap_dartCount (P : PhiData family E) : (phiMap family E).dartCount = 4 * E.card := by
  classical
  let f : (phiMap family E).Dart → {a // a ∈ E} × Bool × Bool :=
    fun y => (⟨phiRegion y, phiRegion_mem y⟩, phiSide y, phiCellSide y)
  have hinj : Function.Injective f := by
    intro y z h
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
    exact dart_ext h.1 h.2.1 h.2.2
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨a, ha⟩, s, o⟩
    refine ⟨phiDart P a ha s o, ?_⟩
    obtain ⟨hr, hs, ho⟩ := P.phi_eq (phiDart P a ha s o) ha (phiDart_cross P a ha s o)
    simp only [f, hr, hs, ho]
  have hcard := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [CombMap.dartCount, hcard, Nat.card_prod, Nat.card_prod,
    Nat.card_eq_fintype_card (α := {a // a ∈ E}), Fintype.card_coe,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  ring

/-- Two cell darts at the same cell share a vertex of `Φ_M`. -/
theorem PhiData.vertexOf_eq_of_cell (P : PhiData family E) {y z : (phiMap family E).Dart}
    (hy : phiCellSide y = true) (hz : phiCellSide z = true)
    (hcell : sideCell (phiRegion y) (phiSide y) = sideCell (phiRegion z) (phiSide z)) :
    (phiMap family E).vertexOf y = (phiMap family E).vertexOf z := by
  rw [phiMap_vertexOf_eq_iff]
  have hyc := phi_cross y
  rw [hy] at hyc
  have hzc := phi_cross z
  rw [hz] at hzc
  have hface := P.face_not_mem_of_cross_true (phiRegion_mem y) hyc
  have hf := faceOf_cross_true (phiRegion y) (P.interior _ (phiRegion_mem y)) hyc
  have hf' := faceOf_cross_true (phiRegion z) (P.interior _ (phiRegion_mem z)) hzc
  exact collapsed_faceOf_eq_of_face_eq hface
    (hf.trans ((congrArg (fun i => (cell Delta i).face) hcell).trans hf'.symm))

/-- Two midpoint darts of the same region share a vertex of `Φ_M`. -/
theorem PhiData.vertexOf_eq_of_midpoint (P : PhiData family E) {y z : (phiMap family E).Dart}
    (hy : phiCellSide y = false) (hz : phiCellSide z = false)
    (hregion : phiRegion y = phiRegion z) :
    (phiMap family E).vertexOf y = (phiMap family E).vertexOf z := by
  rw [phiMap_vertexOf_eq_iff]
  have hyc := phi_cross y
  rw [hy] at hyc
  have hzc := phi_cross z
  rw [hz, ← hregion] at hzc
  have hymem := mem_cycle_cross_false (phiRegion y) (P.interior _ (phiRegion_mem y)) hyc
  have hzmem := mem_cycle_cross_false (phiRegion y) (P.interior _ (phiRegion_mem y)) hzc
  exact collapsed_faceOf_eq_of_mem_cycle P.pairwise (P.subset (phiRegion_mem y)) hymem hzmem

/-- **`Φ_M` subdivided has at most `|V| + |E|` vertices** for a cell set `V` containing the ends of
the regions. -/
theorem phiMap_vertexCount_le (P : PhiData family E) (V : Finset (Fin Delta.rCellCount))
    (hV : ∀ a ∈ E, ∀ s : Bool, sideCell a s ∈ V) :
    (phiMap family E).vertexCount ≤ V.card + E.card := by
  classical
  let S := phiSubdividedGraph P
  let r : (phiMap family E).Dart → {i // i ∈ V} ⊕ {a // a ∈ E} := fun y =>
    if phiCellSide y = true then
      Sum.inl ⟨sideCell (phiRegion y) (phiSide y), hV _ (phiRegion_mem y) _⟩
    else Sum.inr ⟨phiRegion y, phiRegion_mem y⟩
  have hr : ∀ y z : (phiMap family E).Dart,
      (phiMap family E).vertexOf y = (phiMap family E).vertexOf z → r y = r z := by
    intro y z hyz
    have htype : (phiCellSide y = true ↔ phiCellSide z = true) := S.cellDart_of_vertex y z hyz
    by_cases hy : phiCellSide y = true
    · have hz : phiCellSide z = true := htype.mp hy
      have hend := S.endCell_of_vertex y z hy hz hyz
      simp only [r, if_pos hy, if_pos hz]
      exact congrArg Sum.inl (Subtype.ext hend)
    · have hz : ¬ phiCellSide z = true := fun h => hy (htype.mpr h)
      have hreg := S.region_of_vertex y z hy hz hyz
      simp only [r, if_neg hy, if_neg hz]
      exact congrArg Sum.inr (Subtype.ext hreg)
  let g : (phiMap family E).Vertex → {i // i ∈ V} ⊕ {a // a ∈ E} :=
    Quotient.lift r fun y z h => hr y z (((phiMap family E).vertexOf_eq_iff y z).mpr h)
  have hginj : Function.Injective g := by
    intro v₁ v₂ h
    induction v₁ using Quotient.inductionOn' with
    | h y =>
    induction v₂ using Quotient.inductionOn' with
    | h z =>
    change r y = r z at h
    change (phiMap family E).vertexOf y = (phiMap family E).vertexOf z
    by_cases hy : phiCellSide y = true
    · by_cases hz : phiCellSide z = true
      · simp only [r, if_pos hy, if_pos hz, Sum.inl.injEq, Subtype.mk.injEq] at h
        exact P.vertexOf_eq_of_cell hy hz h
      · simp only [r, if_pos hy, if_neg hz, reduceCtorEq] at h
    · by_cases hz : phiCellSide z = true
      · simp only [r, if_neg hy, if_pos hz, reduceCtorEq] at h
      · simp only [r, if_neg hy, if_neg hz, Sum.inr.injEq, Subtype.mk.injEq] at h
        exact P.vertexOf_eq_of_midpoint (by simpa using hy) (by simpa using hz) h
  have hle := Nat.card_le_card_of_injective g hginj
  rw [Nat.card_sum, Nat.card_eq_fintype_card (α := {i // i ∈ V}), Fintype.card_coe,
    Nat.card_eq_fintype_card (α := {a // a ∈ E}), Fintype.card_coe] at hle
  exact hle

end GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.phiMap_dartCount
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.PhiData.vertexOf_eq_of_cell
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.PhiData.vertexOf_eq_of_midpoint
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.phiMap_vertexCount_le
