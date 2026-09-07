import GroupApproximation.GGT.VanKampen.Estimating.RegionCandidate
import GroupApproximation.GGT.VanKampen.Estimating.ContiguityGeometryTransport

/-!
# Retain actual candidate weights and compatible families under insertion

The unrestricted region candidate retains
the transported witness. Its weight is preserved, and distinct witnesses
remain distinct because the full dart and cell maps are injective.
Self-contiguities are included in this transport.
-/

namespace GroupApproximation.GGT.VanKampen.DiscEmbeddingAway

open Embedded
universe u w v v'
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W} {Xi : DiscDiagram.{u, w, v'} W}
  {f : Delta.toCombMap.Face} (E : DiscEmbeddingAway Delta Xi f)
  (C : Surgery.OrderedRCellMap Delta Xi E.faces)
  (hcells : ∀ cell ∈ Delta.relatorCells, cell.face ≠ f) (hf : f ≠ Delta.outerFace)

theorem contiguityGeometry_injective {s : Finset Delta.toCombMap.Face} (hs : f ∉ s) :
    Function.Injective (E.contiguityGeometry C hcells hf hs :
      ContiguityGeometry D eps Delta s → ContiguityGeometry D eps Xi (E.faceSet s)) := by
  intro H K h
  apply ContiguityGeometry.eq_of_data
  · exact (List.map_injective_iff.mpr E.darts.injective) (congrArg (fun J => J.boundary.cycle) h)
  · exact C.indexEquiv.injective (congrArg (fun J => J.source) h)
  · exact (Equiv.optionCongr C.indexEquiv).injective (congrArg (fun J => J.target) h)
  · simpa only [contiguityGeometry, CyclicArc.mapTo_start] using
      congrArg (fun J => J.sourceArc.start.val) h
  · simpa only [contiguityGeometry_source_length] using congrArg (fun J => J.sourceArc.length) h
  · simpa only [contiguityGeometry, CyclicArc.mapTo_start] using
      congrArg (fun J => J.targetArc.start.val) h
  · simpa only [contiguityGeometry_target_length] using congrArg (fun J => J.targetArc.length) h
  · exact (List.map_injective_iff.mpr E.darts.injective) (congrArg (fun J => J.rightSide) h)
  · exact (List.map_injective_iff.mpr E.darts.injective) (congrArg (fun J => J.leftSide) h)

def regionCandidate
    (a : { a : RegionCandidate D eps Delta // f ∉ a.1 }) : RegionCandidate D eps Xi :=
  ⟨E.faceSet a.val.1, E.contiguityGeometry C hcells hf a.property a.val.2⟩

theorem regionCandidate_injective :
    Function.Injective (E.regionCandidate C hcells hf :
      { a : RegionCandidate D eps Delta // f ∉ a.1 } → RegionCandidate D eps Xi) := by
  rintro ⟨⟨s, H⟩, hs⟩ ⟨⟨t, K⟩, ht⟩ h
  have hfaces : E.faceSet s = E.faceSet t := congrArg Sigma.fst h
  have hst : s = t := Finset.map_injective E.faces hfaces
  subst t
  have hcont : E.contiguityGeometry C hcells hf hs H = E.contiguityGeometry C hcells hf ht K :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hHK := E.contiguityGeometry_injective C hcells hf hs hcont
  cases hHK
  rfl

theorem regionCandidate_weight
    (a : { a : RegionCandidate D eps Delta // f ∉ a.1 }) :
    RegionCandidate.weight (E.regionCandidate C hcells hf a) =
      RegionCandidate.weight a.val := by
  exact congrArg₂ Nat.add
    (E.contiguityGeometry_source_length C hcells hf a.property a.val.2)
    (E.contiguityGeometry_target_length C hcells hf a.property a.val.2)

theorem regionCandidate_compatible
    (a b : { a : RegionCandidate D eps Delta // f ∉ a.1 }) :
    RegionCandidate.Compatible (E.regionCandidate C hcells hf a)
        (E.regionCandidate C hcells hf b) ↔ RegionCandidate.Compatible a.val b.val :=
  E.faceSet_disjoint_iff a.val.1 b.val.1

def regionFamilyEmbedding (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) : family ↪ RegionCandidate D eps Xi where
  toFun a := E.regionCandidate C hcells hf ⟨a.val, havoid a.val a.property⟩
  inj' a b h := by
    apply Subtype.ext
    exact congrArg (fun x : { a : RegionCandidate D eps Delta // f ∉ a.1 } => x.val)
      (E.regionCandidate_injective C hcells hf h)

def regionFamily (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) : Finset (RegionCandidate D eps Xi) :=
  family.attach.map (E.regionFamilyEmbedding C hcells hf family havoid)

theorem regionFamily_faces (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) {a : RegionCandidate D eps Xi}
    (ha : a ∈ E.regionFamily C hcells hf family havoid) :
    ∃ b ∈ family, a.1 = E.faceSet b.1 := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  exact ⟨b.val, b.property, rfl⟩

theorem regionFamily_card (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) :
    (E.regionFamily C hcells hf family havoid).card = family.card := by
  simp only [regionFamily, Finset.card_map, Finset.card_attach]

theorem regionFamily_weight (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) :
    EstimatingSelection.familyWeight RegionCandidate.weight
        (E.regionFamily C hcells hf family havoid) =
      EstimatingSelection.familyWeight RegionCandidate.weight family := by
  unfold EstimatingSelection.familyWeight regionFamily
  rw [Finset.sum_map]
  trans ∑ a ∈ family.attach, RegionCandidate.weight a.val
  · apply Finset.sum_congr rfl
    intro a _
    exact E.regionCandidate_weight C hcells hf ⟨a.val, havoid a.val a.property⟩
  · exact Finset.sum_attach _ _

theorem regionFamily_pairwise (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1)
    (hcompat : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family) :
    EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible
      (E.regionFamily C hcells hf family havoid) := by
  intro x hx y hy hne
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
  apply (E.regionCandidate_compatible C hcells hf
    ⟨a.val, havoid a.val a.property⟩ ⟨b.val, havoid b.val b.property⟩).mpr
  apply hcompat a.val a.property b.val b.property
  intro hab
  exact hne (congrArg (E.regionFamilyEmbedding C hcells hf family havoid) (Subtype.ext hab))

end GroupApproximation.GGT.VanKampen.DiscEmbeddingAway

#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.regionCandidate_injective
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.regionFamily_card
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.regionFamily_weight
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.regionFamily_pairwise
