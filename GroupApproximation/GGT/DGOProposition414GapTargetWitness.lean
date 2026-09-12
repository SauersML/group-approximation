import GroupApproximation.GGT.DGOProposition414FiniteComponentFile

/-!
# Target witnesses for DGO Proposition 4.14 gap cycles

The remaining Proposition 4.14 producer must prove component maximality and
isolation for every distinguished target of each auxiliary gap cycle.  This
module names that target-only field before the finite all-component file is
constructed.  The witness is strictly smaller than a complete component file:
it has no exhaustion or target-vs-all separation field.  The constructor from
`DGOProposition414FiniteComponentFile` then promotes it to the full finite
configuration.  A one-component auxiliary cycle supplies a nonempty model.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- Component and isolation data for the distinguished targets of one
auxiliary gap cycle.  This is the target field left open in the uniform
Proposition 4.14 producer, before exhaustion and same-label separation are
assembled into `AuxiliaryCycleComponentConfiguration`. -/
def TargetIsolationWitness
    (D : RelGenSet G Λ) (v : G)
    (left arc right chord : List (RelLetter G Λ)) (nArc : ℕ)
    (arcCut : ℕ → ℕ) (Target : Finset ℕ) (label : ℕ → Λ) : Prop :=
  ∀ s ∈ Target,
    IsComp (label s) (auxiliaryCycleWord left arc right chord)
      (auxiliaryCycleCut left nArc arcCut right s)
      (auxiliaryCycleCut left nArc arcCut right (s + 1)) ∧
    IsIsolated D.fam (label s) v
      (auxiliaryCycleWord left arc right chord)
      (auxiliaryCycleCut left nArc arcCut right s)

/-- A target witness feeds the canonical finite component-file constructor.
This is the packaging step after the four path cases of DGO Proposition 4.14
have supplied the target components and their isolation. -/
noncomputable def AuxiliaryCycleComponentConfiguration.ofTargetIsolationWitness
    {D : RelGenSet G Λ} {v : G}
    {left arc right chord : List (RelLetter G Λ)} {nArc : ℕ}
    {arcCut : ℕ → ℕ} {Target : Finset ℕ} {label : ℕ → Λ}
    (h : TargetIsolationWitness D v left arc right chord nArc arcCut Target label) :
    AuxiliaryCycleComponentConfiguration D v left arc right chord
      nArc arcCut Target label := by
  exact AuxiliaryCycleComponentConfiguration.ofTargetIsolated
    (fun s hs => (h s hs).1) (fun s hs => (h s hs).2)

/-- The target fields of a complete component file form a target witness. -/
theorem targetIsolationWitness_of_configuration
    {D : RelGenSet G Λ} {v : G}
    {left arc right chord : List (RelLetter G Λ)} {nArc : ℕ}
    {arcCut : ℕ → ℕ} {Target : Finset ℕ} {label : ℕ → Λ}
    (C : AuxiliaryCycleComponentConfiguration D v left arc right chord
      nArc arcCut Target label) :
    TargetIsolationWitness D v left arc right chord nArc arcCut Target label := by
  intro s hs
  exact ⟨C.targetComponent s hs, C.targetIsolated s hs⟩

/-! ## A nonempty one-component model -/

private def dgo414WitnessModelRelGenSet : RelGenSet PUnit Unit where
  base := Set.univ
  fam := fun _ => ⊤
  symmetricGenerating := by
    have h := Hyperbolic.isSymmetricGeneratingSet_univ (G := PUnit)
    rw [Finset.coe_univ] at h
    simpa only [Set.univ_union] using h

private def dgo414WitnessModelWord : List (RelLetter PUnit Unit) :=
  [RelLetter.comp () ()]

private def dgo414WitnessModelCut : ℕ → ℕ := fun s => s

private def dgo414WitnessModelLabel : ℕ → Unit := fun _ => ()

private def dgo414WitnessModelTarget : Finset ℕ := {0}

/-- The one-letter auxiliary cycle has a genuine target component. -/
private theorem dgo414WitnessModel_component :
    IsComp () dgo414WitnessModelWord 0 1 := by
  refine ⟨by omega, by simp [dgo414WitnessModelWord], ?_, ?_, ?_⟩
  · intro j hj hkj hjlt
    have hj0 : j = 0 := by omega
    subst j
    exact rfl
  · intro j hj hjlt
    omega
  · intro hk hklt
    have hlen : dgo414WitnessModelWord.length = 1 := by
      rfl
    rw [hlen] at hk
    omega

/-- The one-letter auxiliary cycle has an isolated target component. -/
private theorem dgo414WitnessModel_isolated :
    IsIsolated dgo414WitnessModelRelGenSet.fam () (1 : PUnit)
      dgo414WitnessModelWord 0 := by
  refine ⟨⟨1, dgo414WitnessModel_component⟩, ?_⟩
  intro j hne hstart hconn
  obtain ⟨k, hcomp⟩ := hstart
  have hjlt : j < dgo414WitnessModelWord.length := by
    exact hcomp.1.trans_le hcomp.2.1
  have hj0 : j = 0 := by
    simpa [dgo414WitnessModelWord] using hjlt
  exact hne hj0

/-- The target witness is inhabited on a nonempty auxiliary cycle, so the
model does not rely on an empty target or a missing component. -/
theorem targetIsolationWitness_trivialModel :
    TargetIsolationWitness dgo414WitnessModelRelGenSet (1 : PUnit)
      [] [] [] dgo414WitnessModelWord 0 dgo414WitnessModelCut
      dgo414WitnessModelTarget dgo414WitnessModelLabel := by
  intro s hs
  have hs0 : s = 0 := by simpa [dgo414WitnessModelTarget] using hs
  subst s
  have hword : auxiliaryCycleWord ([] : List (RelLetter PUnit Unit)) [] []
      dgo414WitnessModelWord = dgo414WitnessModelWord := by
    rfl
  have hcut0 : auxiliaryCycleCut ([] : List (RelLetter PUnit Unit)) 0
      dgo414WitnessModelCut [] 0 = 0 := by
    simp [auxiliaryCycleCut, appendCut]
  have hcut1 : auxiliaryCycleCut ([] : List (RelLetter PUnit Unit)) 0
      dgo414WitnessModelCut [] (0 + 1) = 1 := by
    simp [auxiliaryCycleCut, appendCut]
  constructor
  · rw [hword, hcut0, hcut1]
    simpa [dgo414WitnessModelLabel] using dgo414WitnessModel_component
  · rw [hword, hcut0]
    simpa [dgo414WitnessModelLabel] using dgo414WitnessModel_isolated

/-- The finite component-file constructor is inhabited in the same model. -/
theorem targetIsolationConfiguration_trivialModel :
    Nonempty (AuxiliaryCycleComponentConfiguration
      dgo414WitnessModelRelGenSet (1 : PUnit)
      ([] : List (RelLetter PUnit Unit)) [] [] dgo414WitnessModelWord 0
      dgo414WitnessModelCut dgo414WitnessModelTarget dgo414WitnessModelLabel) := by
  exact ⟨AuxiliaryCycleComponentConfiguration.ofTargetIsolationWitness
    targetIsolationWitness_trivialModel⟩

end DGOProposition414
end GGT
end GroupApproximation
