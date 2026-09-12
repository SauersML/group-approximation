import GroupApproximation.GGT.DGOProposition414ConnectorProducer

/-!
# Canonical child ownership of broken balanced components

The greedy index stores source positions rather than original component
indices.  This file recovers the unique original source at every entry and,
conversely, the unique entry (hence an actual child index) owned by every
broken source.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace HalfEntry

/-- The original broken source represented by a greedy-list entry. -/
noncomputable def entrySource
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L)
    (j : Fin A.sources.length) : ℕ :=
  Classical.choose (A.entries j j.isLt)

theorem entrySource_mem
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L)
    (j : Fin A.sources.length) : entrySource A j ∈ I :=
  (Classical.choose_spec (A.entries j j.isLt)).1

theorem source_getElem_eq_pos_entrySource
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L)
    (j : Fin A.sources.length) :
    A.sources[j] = pos (entrySource A j) :=
  (Classical.choose_spec (A.entries j j.isLt)).2.1

theorem partner_getElem_eq_partner_entrySource
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L)
    (j : Fin A.sources.length) :
    A.partners[j.val]? = some (partner (entrySource A j)) :=
  (Classical.choose_spec (A.entries j j.isLt)).2.2

/-- The interval immediately indexed by a source entry is an actual member of
the `sources.length + 1` child family. -/
def entryChild
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L)
    (j : Fin A.sources.length) : Fin A.pieceCount :=
  ⟨j, by simp [DGOPolygonCut.GreedyHalfFamilyIndex.pieceCount]⟩

/-- The gap interval immediately after a source entry.  Together with
`entryChild`, this is the adjacent pair containing respectively the source's
start connector on the right and end connector on the left. -/
def exitChild
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L)
    (j : Fin A.sources.length) : Fin A.pieceCount :=
  ⟨j + 1, by simp [DGOPolygonCut.GreedyHalfFamilyIndex.pieceCount]⟩

theorem entryChild_ne_exitChild
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L)
    (j : Fin A.sources.length) : entryChild A j ≠ exitChild A j := by
  intro h
  have := congrArg Fin.val h
  simp [entryChild, exitChild] at this

end HalfEntry

namespace BalancedSplitData

private theorem exists_firstSourceEntry
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    ∃ j : Fin B.brokenAssignment.index.first.sources.length,
      HalfEntry.entrySource B.brokenAssignment.index.first j = s := by
  let A := B.brokenAssignment.index.first
  have hsSource : B.componentPlacement.firstPos s ∈ A.sources :=
    (A.source_mem _).mpr ⟨s, hs, rfl⟩
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hsSource
  let jf : Fin A.sources.length := ⟨j, hj⟩
  refine ⟨jf, ?_⟩
  apply B.componentPlacement.firstPos_injective
  · exact (mem_brokenSet_iff.mp (HalfEntry.entrySource_mem A jf)).1
  · exact (mem_brokenSet_iff.mp hs).1
  · rw [← HalfEntry.source_getElem_eq_pos_entrySource A jf]
    exact hget

private theorem exists_secondSourceEntry
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    ∃ j : Fin B.brokenAssignment.index.second.sources.length,
      HalfEntry.entrySource B.brokenAssignment.index.second j = s := by
  let A := B.brokenAssignment.index.second
  have hsSource : B.componentPlacement.secondPos s ∈ A.sources :=
    (A.source_mem _).mpr ⟨s, hs, rfl⟩
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hsSource
  let jf : Fin A.sources.length := ⟨j, hj⟩
  refine ⟨jf, ?_⟩
  apply B.componentPlacement.secondPos_injective
  · exact (mem_brokenSet_iff.mp (HalfEntry.entrySource_mem A jf)).1
  · exact (mem_brokenSet_iff.mp hs).1
  · rw [← HalfEntry.source_getElem_eq_pos_entrySource A jf]
    exact hget

/-- The unique first-half greedy entry of a broken source. -/
noncomputable def firstSourceEntry
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    Fin B.brokenAssignment.index.first.sources.length :=
  Classical.choose (B.exists_firstSourceEntry s hs)

theorem firstSourceEntry_source
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    HalfEntry.entrySource B.brokenAssignment.index.first
      (B.firstSourceEntry s hs) = s :=
  Classical.choose_spec (B.exists_firstSourceEntry s hs)

theorem firstSourceEntry_partner
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    B.brokenAssignment.index.first.partners[(B.firstSourceEntry s hs).val]? =
      some (B.brokenAssignment.first.partner s) := by
  rw [HalfEntry.partner_getElem_eq_partner_entrySource,
    B.firstSourceEntry_source s hs]

/-- The unique wrapped-half greedy entry of a broken source. -/
noncomputable def secondSourceEntry
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    Fin B.brokenAssignment.index.second.sources.length :=
  Classical.choose (B.exists_secondSourceEntry s hs)

theorem secondSourceEntry_source
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    HalfEntry.entrySource B.brokenAssignment.index.second
      (B.secondSourceEntry s hs) = s :=
  Classical.choose_spec (B.exists_secondSourceEntry s hs)

theorem secondSourceEntry_partner
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    B.brokenAssignment.index.second.partners[(B.secondSourceEntry s hs).val]? =
      some (B.brokenAssignment.second.partner s) := by
  rw [HalfEntry.partner_getElem_eq_partner_entrySource,
    B.secondSourceEntry_source s hs]

/-- The actual first-half child owned by a broken source. -/
noncomputable def firstBrokenOwner
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    Fin B.brokenAssignment.index.first.pieceCount :=
  HalfEntry.entryChild B.brokenAssignment.index.first (B.firstSourceEntry s hs)

/-- The actual wrapped-half child owned by a broken source. -/
noncomputable def secondBrokenOwner
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    Fin B.brokenAssignment.index.second.pieceCount :=
  HalfEntry.entryChild B.brokenAssignment.index.second (B.secondSourceEntry s hs)

theorem firstBrokenOwner_injective
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    {s t : ℕ}
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives)
    (ht : t ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives)
    (howner : B.firstBrokenOwner s hs = B.firstBrokenOwner t ht) : s = t := by
  have hentry : B.firstSourceEntry s hs = B.firstSourceEntry t ht := by
    have hval := congrArg
      (fun x : Fin B.brokenAssignment.index.first.pieceCount => x.val) howner
    apply Fin.ext
    exact hval
  rw [← B.firstSourceEntry_source s hs, ← B.firstSourceEntry_source t ht,
    hentry]

theorem secondBrokenOwner_injective
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    {s t : ℕ}
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives)
    (ht : t ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives)
    (howner : B.secondBrokenOwner s hs = B.secondBrokenOwner t ht) : s = t := by
  have hentry : B.secondSourceEntry s hs = B.secondSourceEntry t ht := by
    have hval := congrArg
      (fun x : Fin B.brokenAssignment.index.second.pieceCount => x.val) howner
    apply Fin.ext
    exact hval
  rw [← B.secondSourceEntry_source s hs, ← B.secondSourceEntry_source t ht,
    hentry]

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
