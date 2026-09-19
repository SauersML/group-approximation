import GroupApproximation.GGT.DGOProposition414Assembly

/-!
# A finite component file from already proved target isolation

Once the concrete child geometry proves that its target components are
isolated, no further geometric input is needed to populate
`AuxiliaryCycleComponentConfiguration`.  This module enumerates the finitely
many same-label component starts by target/position pairs and derives the
configuration's exhaustion and separation fields directly from isolation.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace AuxiliaryCycleComponentConfiguration

/-- A finite auxiliary-cycle component file is canonical once every target
component and its isolation have been established. -/
noncomputable def ofTargetIsolated
    {D : RelGenSet G Λ} {v : G}
    {left arc right chord : List (RelLetter G Λ)} {nArc : ℕ}
    {arcCut : ℕ → ℕ} {Target : Finset ℕ} {label : ℕ → Λ}
    (htarget : ∀ s ∈ Target,
      IsComp (label s) (auxiliaryCycleWord left arc right chord)
        (auxiliaryCycleCut left nArc arcCut right s)
        (auxiliaryCycleCut left nArc arcCut right (s + 1)))
    (hisolated : ∀ s ∈ Target,
      IsIsolated D.fam (label s) v
        (auxiliaryCycleWord left arc right chord)
        (auxiliaryCycleCut left nArc arcCut right s)) :
    AuxiliaryCycleComponentConfiguration D v left arc right chord
      nArc arcCut Target label := by
  classical
  let word := auxiliaryCycleWord left arc right chord
  let startsFor : ℕ → Finset ℕ := fun s =>
    (Finset.range word.length).filter fun q =>
      IsCompStart (label s) word q
  let all : Finset ℕ := Target.biUnion fun s =>
    (startsFor s).image fun q => Nat.pair s q
  refine
    { all := all
      allLabel := fun t => label (Nat.unpair t).1
      allPos := fun t => (Nat.unpair t).2
      targetComponent := htarget
      exhaust := ?_
      separated := ?_ }
  · intro s hs q hq
    have hqlt : q < word.length := by
      obtain ⟨qend, hcomp⟩ := hq
      exact hcomp.1.trans_le hcomp.2.1
    refine ⟨Nat.pair s q, ?_, ?_, ?_⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨s, hs, Finset.mem_image.mpr ⟨q, ?_, rfl⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqlt, hq⟩
    · simp
    · simp
  · intro s hs t ht hlabel hpos hconn
    obtain ⟨r, hr, ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨q, hq, hpair⟩ := Finset.mem_image.mp ht
    have hqstart : IsCompStart (label r) word q :=
      (Finset.mem_filter.mp hq).2
    subst t
    simp only [Nat.unpair_pair] at hlabel hpos hconn
    have hqstart' : IsCompStart (label s) word q := by
      simpa only [hlabel] using hqstart
    exact (hisolated s hs).2 q hpos hqstart' hconn

end AuxiliaryCycleComponentConfiguration

end DGOProposition414
end GGT
end GroupApproximation
