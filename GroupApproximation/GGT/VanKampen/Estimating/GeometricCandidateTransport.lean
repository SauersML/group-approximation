import GroupApproximation.GGT.VanKampen.Estimating.GeometricCandidate
import GroupApproximation.GGT.VanKampen.Estimating.ContiguityTransport

/-!
# Retain actual candidate weights and compatible families under insertion

Unlike the historical face-only candidate, the geometric candidate retains
the transported witness. Its weight is preserved, and distinct witnesses
remain distinct because the full dart and cell maps are injective.
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

theorem contiguity_injective {s : Finset Delta.toCombMap.Face} (hs : f ∉ s) :
    Function.Injective (E.contiguity C hcells hf hs :
      Contiguity D eps Delta s → Contiguity D eps Xi (E.faceSet s)) := by
  intro H K h
  apply Contiguity.eq_of_data
  · exact (List.map_injective_iff.mpr E.darts.injective) (congrArg (fun J => J.boundary.cycle) h)
  · exact C.indexEquiv.injective (congrArg (fun J => J.source) h)
  · exact (Equiv.optionCongr C.indexEquiv).injective (congrArg (fun J => J.target) h)
  · simpa only [contiguity, CyclicArc.mapTo_start] using
      congrArg (fun J => J.sourceArc.start.val) h
  · simpa only [contiguity_source_length] using congrArg (fun J => J.sourceArc.length) h
  · simpa only [contiguity, CyclicArc.mapTo_start] using
      congrArg (fun J => J.targetArc.start.val) h
  · simpa only [contiguity_target_length] using congrArg (fun J => J.targetArc.length) h
  · exact (List.map_injective_iff.mpr E.darts.injective) (congrArg (fun J => J.rightSide) h)
  · exact (List.map_injective_iff.mpr E.darts.injective) (congrArg (fun J => J.leftSide) h)

def geometricCandidate
    (a : { a : GeometricCandidate D eps Delta // f ∉ a.1 }) : GeometricCandidate D eps Xi :=
  ⟨E.faceSet a.val.1, E.contiguity C hcells hf a.property a.val.2⟩

theorem geometricCandidate_injective :
    Function.Injective (E.geometricCandidate C hcells hf :
      { a : GeometricCandidate D eps Delta // f ∉ a.1 } → GeometricCandidate D eps Xi) := by
  rintro ⟨⟨s, H⟩, hs⟩ ⟨⟨t, K⟩, ht⟩ h
  have hfaces : E.faceSet s = E.faceSet t := congrArg Sigma.fst h
  have hst : s = t := Finset.map_injective E.faces hfaces
  subst t
  have hcont : E.contiguity C hcells hf hs H = E.contiguity C hcells hf ht K :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hHK := E.contiguity_injective C hcells hf hs hcont
  cases hHK
  rfl

theorem geometricCandidate_weight
    (a : { a : GeometricCandidate D eps Delta // f ∉ a.1 }) :
    GeometricCandidate.weight (E.geometricCandidate C hcells hf a) =
      GeometricCandidate.weight a.val := by
  exact congrArg₂ Nat.add
    (E.contiguity_source_length C hcells hf a.property a.val.2)
    (E.contiguity_target_length C hcells hf a.property a.val.2)

theorem geometricCandidate_compatible
    (a b : { a : GeometricCandidate D eps Delta // f ∉ a.1 }) :
    GeometricCandidate.Compatible (E.geometricCandidate C hcells hf a)
        (E.geometricCandidate C hcells hf b) ↔ GeometricCandidate.Compatible a.val b.val :=
  E.faceSet_disjoint_iff a.val.1 b.val.1

def geometricFamilyEmbedding (family : Finset (GeometricCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) : family ↪ GeometricCandidate D eps Xi where
  toFun a := E.geometricCandidate C hcells hf ⟨a.val, havoid a.val a.property⟩
  inj' a b h := by
    apply Subtype.ext
    exact congrArg (fun x : { a : GeometricCandidate D eps Delta // f ∉ a.1 } => x.val)
      (E.geometricCandidate_injective C hcells hf h)

def geometricFamily (family : Finset (GeometricCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) : Finset (GeometricCandidate D eps Xi) :=
  family.attach.map (E.geometricFamilyEmbedding C hcells hf family havoid)

theorem geometricFamily_faces (family : Finset (GeometricCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) {a : GeometricCandidate D eps Xi}
    (ha : a ∈ E.geometricFamily C hcells hf family havoid) :
    ∃ b ∈ family, a.1 = E.faceSet b.1 := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  exact ⟨b.val, b.property, rfl⟩

theorem geometricFamily_card (family : Finset (GeometricCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) :
    (E.geometricFamily C hcells hf family havoid).card = family.card := by
  simp only [geometricFamily, Finset.card_map, Finset.card_attach]

theorem geometricFamily_weight (family : Finset (GeometricCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) :
    EstimatingSelection.familyWeight GeometricCandidate.weight
        (E.geometricFamily C hcells hf family havoid) =
      EstimatingSelection.familyWeight GeometricCandidate.weight family := by
  unfold EstimatingSelection.familyWeight geometricFamily
  rw [Finset.sum_map]
  trans ∑ a ∈ family.attach, GeometricCandidate.weight a.val
  · apply Finset.sum_congr rfl
    intro a _
    exact E.geometricCandidate_weight C hcells hf ⟨a.val, havoid a.val a.property⟩
  · exact Finset.sum_attach _ _

theorem geometricFamily_pairwise (family : Finset (GeometricCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1)
    (hcompat : EstimatingSelection.PairwiseCompatible GeometricCandidate.Compatible family) :
    EstimatingSelection.PairwiseCompatible GeometricCandidate.Compatible
      (E.geometricFamily C hcells hf family havoid) := by
  intro x hx y hy hne
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
  apply (E.geometricCandidate_compatible C hcells hf
    ⟨a.val, havoid a.val a.property⟩ ⟨b.val, havoid b.val b.property⟩).mpr
  apply hcompat a.val a.property b.val b.property
  intro hab
  exact hne (congrArg (E.geometricFamilyEmbedding C hcells hf family havoid) (Subtype.ext hab))

end GroupApproximation.GGT.VanKampen.DiscEmbeddingAway

#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.geometricCandidate_injective
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.geometricFamily_card
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.geometricFamily_weight
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.geometricFamily_pairwise
