import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionCounting
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.GGT.VanKampen.GFaceQuadrilateralRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# Exterior regions across a region correspondence

The surgeries that move a distinguished section family to an O-equivalent copy
(`OuterSpurThickeningStatement`, `OuterCellThickening.OuterCellThickeningStatement`) return a
bijection `e` between the old and the new regions that keeps target profiles and source indices.
Osin's proof of Lemma 9.7(b) starts from two distinct exterior regions of one cell to one section
(`PocketWalk.exists_pocketFaceSet_of_exteriorAt_of_value`).  This file moves such a pair to the
copy.

* `mem_exteriorAt`: an exterior region of a cell goes to an exterior region of the cell with the
  same index.
* `targetsSectionIndex`: a region to section `j` goes to a region to section `j`.
* `val_ne`: distinct regions go to distinct regions.
* `exists_exteriorPair`: the three together, for a pair of distinct exterior regions of one cell
  to one section.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.RegionProfileTransport

open Embedded

universe u w v v'

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W} {Xi : DiscDiagram.{u, w, v'} W}

/-- **An exterior region of a cell goes to an exterior region of the cell with the same index**,
across a region correspondence that keeps target profiles and source indices. -/
theorem mem_exteriorAt {selected : Finset (RegionCandidate D eps Delta)}
    {selected' : Finset (RegionCandidate D eps Xi)} (e : selected ≃ selected')
    (he : ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
      (e a).1.2.source.val = a.1.2.source.val)
    {i : Fin Delta.rCellCount} {i' : Fin Xi.rCellCount} (hi : i'.val = i.val)
    (a : selected) (ha : a.1 ∈ RegionCandidate.exteriorAt selected i) :
    (e a).1 ∈ RegionCandidate.exteriorAt selected' i' := by
  obtain ⟨hkind, hsource⟩ := Finset.mem_filter.mp ha
  obtain ⟨-, hext⟩ := Finset.mem_filter.mp hkind
  obtain ⟨hprof, hsrc⟩ := he a
  have ht : a.1.2.target = none := by
    cases h : a.1.2.target with
    | none => rfl
    | some _ => simp [h] at hext
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(e a).2, ?_⟩, ?_⟩
  · simp [hprof.1.mpr ht]
  · exact Fin.ext (hsrc.trans ((congrArg Fin.val hsource).trans hi.symm))

/-- **A region to section `j` goes to a region to section `j`** along a same target profile. -/
theorem targetsSectionIndex {lambda c : ℝ} {word : List (RelLetter G Lambda)}
    {cuts : SectionCuts D lambda c word} {j : Fin cuts.count}
    {a : RegionCandidate D eps Xi} {b : RegionCandidate D eps Delta}
    (hab : RegionCandidate.SameTargetProfile a b)
    (hb : RegionCandidate.TargetsSectionIndex cuts j b) :
    RegionCandidate.TargetsSectionIndex cuts j a := by
  unfold RegionCandidate.TargetsSectionIndex at hb ⊢
  refine ⟨hab.1.mpr hb.1, ?_, ?_⟩
  · rw [hab.2.1]
    exact hb.2.1
  · rw [hab.2.1, hab.2.2.1]
    exact hb.2.2

/-- Distinct regions go to distinct regions. -/
theorem val_ne {selected : Finset (RegionCandidate D eps Delta)}
    {selected' : Finset (RegionCandidate D eps Xi)} (e : selected ≃ selected') {a b : selected}
    (hab : a ≠ b) : (e a).1 ≠ (e b).1 :=
  fun h => hab (e.injective (Subtype.ext h))

/-- **A pair of distinct exterior regions of one cell to one section, on the copy.** -/
theorem exists_exteriorPair {selected : Finset (RegionCandidate D eps Delta)}
    {selected' : Finset (RegionCandidate D eps Xi)} (e : selected ≃ selected')
    (he : ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
      (e a).1.2.source.val = a.1.2.source.val)
    {lambda c : ℝ} {word : List (RelLetter G Lambda)} {cuts : SectionCuts D lambda c word}
    {i : Fin Delta.rCellCount} {j : Fin cuts.count} {a b : RegionCandidate D eps Delta}
    (ha : a ∈ RegionCandidate.exteriorAt selected i)
    (hb : b ∈ RegionCandidate.exteriorAt selected i) (hab : a ≠ b)
    (hja : RegionCandidate.TargetsSectionIndex cuts j a)
    (hjb : RegionCandidate.TargetsSectionIndex cuts j b) :
    ∃ (i' : Fin Xi.rCellCount) (a' b' : RegionCandidate D eps Xi),
      i'.val = i.val ∧ a' ∈ RegionCandidate.exteriorAt selected' i' ∧
        b' ∈ RegionCandidate.exteriorAt selected' i' ∧ a' ≠ b' ∧
          RegionCandidate.TargetsSectionIndex cuts j a' ∧
            RegionCandidate.TargetsSectionIndex cuts j b' := by
  have hamem : a ∈ selected := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
  have hbmem : b ∈ selected := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1
  have hsource : a.2.source = i := (Finset.mem_filter.mp ha).2
  have hi : (e ⟨a, hamem⟩).1.2.source.val = i.val :=
    (he ⟨a, hamem⟩).2.trans (congrArg Fin.val hsource)
  exact ⟨(e ⟨a, hamem⟩).1.2.source, (e ⟨a, hamem⟩).1, (e ⟨b, hbmem⟩).1, hi,
    mem_exteriorAt e he hi ⟨a, hamem⟩ ha, mem_exteriorAt e he hi ⟨b, hbmem⟩ hb,
    val_ne e (fun h => hab (congrArg Subtype.val h)),
    targetsSectionIndex (he ⟨a, hamem⟩).1 hja, targetsSectionIndex (he ⟨b, hbmem⟩).1 hjb⟩

end GroupApproximation.GGT.VanKampen.RegionProfileTransport

#audit_axioms GroupApproximation.GGT.VanKampen.RegionProfileTransport.mem_exteriorAt
#audit_axioms GroupApproximation.GGT.VanKampen.RegionProfileTransport.targetsSectionIndex
#audit_axioms GroupApproximation.GGT.VanKampen.RegionProfileTransport.val_ne
#audit_axioms GroupApproximation.GGT.VanKampen.RegionProfileTransport.exists_exteriorPair
