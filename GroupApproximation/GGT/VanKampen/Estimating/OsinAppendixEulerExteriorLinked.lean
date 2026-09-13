import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerExteriorCount
import GroupApproximation.Meta.AxiomGuard

/-!
# Linked components of `Φ'_M` with one outer vertex

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.3.  The Euler count
`card_add_six_le_of_linkedO` (`GGT/VanKampen/Estimating/OsinAppendixEulerExteriorCount.lean`) asks
for a set `V` of ends containing the ends of the regions (`hV`) and for regions linked through
shared ends (`hlinked`).  This module produces both for any set of regions:

* the regions linked to one region through shared ends form a linked set
  (`linked_linkedComponentO`);
* the ends of a set of regions contain the ends of each of its regions (`sideCellO_mem_endCellsO`);
* a region outside the component shares no end with it (`sideCellO_ne_of_not_mem_linkedComponentO`),
  and all regions with an end at the outer vertex lie in one component
  (`mem_linkedComponentO_of_sideCellO_eq_none`);
* `ExtPhiData` passes to subsets (`ExtPhiData.mono`), so the count applies to every component
  (`card_add_six_le_linkedComponentO`).

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

open Equiv
universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {family E : Finset (RegionCandidate D eps Delta)}

/-- `ExtPhiData` passes to a subset of the selected regions. -/
theorem ExtPhiData.mono (P : ExtPhiData family E) {E' : Finset (RegionCandidate D eps Delta)}
    (h : E' ⊆ E) : ExtPhiData family E' where
  subset := h.trans P.subset
  pairwise := P.pairwise
  cell_not_mem := P.cell_not_mem
  nondegenerate a ha := P.nondegenerate a (h ha)
  noLoop a ha := P.noLoop a (h ha)

theorem sharesEndO_symm {a b : RegionCandidate D eps Delta} (h : SharesEndO E a b) :
    SharesEndO E b a := by
  obtain ⟨ha, hb, s, t, hst⟩ := h
  exact ⟨hb, ha, t, s, hst.symm⟩

theorem linkedO_symm {a b : RegionCandidate D eps Delta}
    (h : Relation.ReflTransGen (SharesEndO E) a b) :
    Relation.ReflTransGen (SharesEndO E) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (sharesEndO_symm hbc) ih

/-- **The regions linked to `a₀` through shared ends.** -/
noncomputable def linkedComponentO (E : Finset (RegionCandidate D eps Delta))
    (a₀ : RegionCandidate D eps Delta) : Finset (RegionCandidate D eps Delta) := by
  classical
  exact E.filter fun b => Relation.ReflTransGen (SharesEndO E) a₀ b

theorem mem_linkedComponentO {a₀ b : RegionCandidate D eps Delta} :
    b ∈ linkedComponentO E a₀ ↔ b ∈ E ∧ Relation.ReflTransGen (SharesEndO E) a₀ b := by
  classical
  simp only [linkedComponentO, Finset.mem_filter]

theorem linkedComponentO_subset (E : Finset (RegionCandidate D eps Delta))
    (a₀ : RegionCandidate D eps Delta) : linkedComponentO E a₀ ⊆ E :=
  fun _ hb => (mem_linkedComponentO.mp hb).1

theorem self_mem_linkedComponentO {a₀ : RegionCandidate D eps Delta} (ha₀ : a₀ ∈ E) :
    a₀ ∈ linkedComponentO E a₀ :=
  mem_linkedComponentO.mpr ⟨ha₀, Relation.ReflTransGen.refl⟩

/-- A chain of shared ends from `a₀` stays inside the component of `a₀`. -/
theorem linkedO_linkedComponentO {a₀ b : RegionCandidate D eps Delta}
    (h : Relation.ReflTransGen (SharesEndO E) a₀ b) :
    Relation.ReflTransGen (SharesEndO (linkedComponentO E a₀)) a₀ b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
      obtain ⟨hb, hc, s, t, hst⟩ := hbc
      exact ih.tail ⟨mem_linkedComponentO.mpr ⟨hb, hab⟩,
        mem_linkedComponentO.mpr ⟨hc, hab.tail ⟨hb, hc, s, t, hst⟩⟩, s, t, hst⟩

/-- **The component of a region is linked through shared ends**: the hypothesis `hlinked` of
`card_add_six_le_of_linkedO`. -/
theorem linked_linkedComponentO (E : Finset (RegionCandidate D eps Delta))
    (a₀ : RegionCandidate D eps Delta) :
    ∀ a ∈ linkedComponentO E a₀, ∀ b ∈ linkedComponentO E a₀,
      Relation.ReflTransGen (SharesEndO (linkedComponentO E a₀)) a b := by
  intro a ha b hb
  exact (linkedO_symm (linkedO_linkedComponentO (mem_linkedComponentO.mp ha).2)).trans
    (linkedO_linkedComponentO (mem_linkedComponentO.mp hb).2)

/-- A region sharing an end with a region of the component lies in the component. -/
theorem mem_linkedComponentO_of_sideCellO_eq {a₀ a b : RegionCandidate D eps Delta}
    (ha : a ∈ linkedComponentO E a₀) (hb : b ∈ E) {s t : Bool}
    (hst : sideCellO a s = sideCellO b t) : b ∈ linkedComponentO E a₀ := by
  obtain ⟨haE, ha₀a⟩ := mem_linkedComponentO.mp ha
  exact mem_linkedComponentO.mpr ⟨hb, ha₀a.tail ⟨haE, hb, s, t, hst⟩⟩

/-- **A region outside the component shares no end with it.** -/
theorem sideCellO_ne_of_not_mem_linkedComponentO {a₀ a b : RegionCandidate D eps Delta}
    (ha : a ∈ linkedComponentO E a₀) (hb : b ∈ E) (hbC : b ∉ linkedComponentO E a₀)
    (s t : Bool) : sideCellO a s ≠ sideCellO b t :=
  fun hst => hbC (mem_linkedComponentO_of_sideCellO_eq ha hb hst)

/-- **All regions with an end at the outer vertex lie in one component.** -/
theorem mem_linkedComponentO_of_sideCellO_eq_none {a₀ b : RegionCandidate D eps Delta}
    (ha₀ : a₀ ∈ E) (hb : b ∈ E) {s t : Bool} (ha₀s : sideCellO a₀ s = none)
    (hbt : sideCellO b t = none) : b ∈ linkedComponentO E a₀ :=
  mem_linkedComponentO_of_sideCellO_eq (self_mem_linkedComponentO ha₀) hb (ha₀s.trans hbt.symm)

/-- The ends of a set of regions: relator cells, and the outer vertex `none`. -/
noncomputable def endCellsO (E : Finset (RegionCandidate D eps Delta)) :
    Finset (Option (Fin Delta.rCellCount)) := by
  classical
  exact E.biUnion fun a => {sideCellO a true, sideCellO a false}

theorem mem_endCellsO {i : Option (Fin Delta.rCellCount)} :
    i ∈ endCellsO E ↔ ∃ a ∈ E, ∃ s : Bool, sideCellO a s = i := by
  classical
  simp only [endCellsO, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha, h | h⟩
    · exact ⟨a, ha, true, h.symm⟩
    · exact ⟨a, ha, false, h.symm⟩
  · rintro ⟨a, ha, s, rfl⟩
    exact ⟨a, ha, by cases s <;> simp⟩

/-- **The ends of a set of regions contain the ends of each of its regions**: the hypothesis `hV`
of `card_add_six_le_of_linkedO`. -/
theorem sideCellO_mem_endCellsO {a : RegionCandidate D eps Delta} (ha : a ∈ E) (s : Bool) :
    sideCellO a s ∈ endCellsO E :=
  mem_endCellsO.mpr ⟨a, ha, s, rfl⟩

/-- **Euler's count of `Φ'_M` on the component of a region**: `|C| + 6 ≤ 3|ends of C| + t`, where
`t` counts the faces of degree less than six. -/
theorem card_add_six_le_linkedComponentO (P : ExtPhiData family E)
    {a₀ : RegionCandidate D eps Delta} (ha₀ : a₀ ∈ E) :
    (linkedComponentO E a₀).card + 6 ≤ 3 * (endCellsO (linkedComponentO E a₀)).card +
      (Finset.univ.filter fun f : (phiMapO family (linkedComponentO E a₀)).Face =>
        (phiMapO family (linkedComponentO E a₀)).faceDegree f < 6).card :=
  card_add_six_le_of_linkedO (P.mono (linkedComponentO_subset E a₀))
    (endCellsO (linkedComponentO E a₀)) (fun _ ha s => sideCellO_mem_endCellsO ha s)
    ⟨a₀, self_mem_linkedComponentO ha₀⟩ (linked_linkedComponentO E a₀)

end GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.mono
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.linkedO_symm
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.linked_linkedComponentO
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.sideCellO_ne_of_not_mem_linkedComponentO
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.mem_linkedComponentO_of_sideCellO_eq_none
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.sideCellO_mem_endCellsO
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.card_add_six_le_linkedComponentO
