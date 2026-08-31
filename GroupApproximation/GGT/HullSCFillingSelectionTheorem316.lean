import GroupApproximation.GGT.HullSCFillingNonElementary
import GroupApproximation.GGT.HullTheorem316Assembly

/-!
# Simultaneous filling peripherals from Hull's proved Theorem 3.16 geometry

The old simultaneous-selection assembly consumed `HeGXFamily` as a separate
literature input.  The quantitative Theorem 3.16 assembly now proves precisely
that finite-family embedding.  This file removes `HeGXFamily` from the filling
lane: once `yi` has chosen a simultaneous cyclic family, all its pair cores and
the flattened auxiliary family are hyperbolically embedded unconditionally.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- The simultaneous `yi` witnesses produce the auxiliary family required by
Hull Lemma 4.4, using the formalized Theorem 3.16 rather than a separate
`HeGXFamily` premise. -/
theorem simultaneousAuxiliaryPeripheralSelection_of_yi_theorem316
    (hyi : SimultaneousYiSuitableFamily.{u}) :
    SimultaneousAuxiliaryPeripheralSelection.{u} := by
  intro G _ A N k S hN hS
  obtain ⟨g, hg, hlox, hnc, hcyc⟩ := hyi A S hN hS
  let gN : Bool → G := fun b => g (none, b)
  let gS : Fin k → Bool → G := fun j b => g (some j, b)
  have hgN : ∀ b, gN b ∈ N := by
    intro b
    simpa [gN, AuxiliaryTarget] using hg (none, b)
  have hgS : ∀ j b, gS j b ∈ S j := by
    intro j b
    simpa [gS, AuxiliaryTarget] using hg (some j, b)
  have hloxN : ∀ b, IsLoxodromic (gN b) (Cayley.base A.alphabet) :=
    fun b => hlox (none, b)
  have hloxS : ∀ j b, IsLoxodromic (gS j b) (Cayley.base A.alphabet) :=
    fun j b => hlox (some j, b)
  have hncN : PairwiseNonCommensurable gN := by
    intro b c hbc p q hp hq t
    have hne : ((none, b) : AuxiliaryPeripheralIndex k) ≠ (none, c) := by
      intro heq
      exact hbc (congrArg Prod.snd heq)
    exact hnc (none, b) (none, c) hne p q hp hq t
  have hncS : ∀ j, PairwiseNonCommensurable (gS j) := by
    intro j b c hbc p q hp hq t
    have hne : ((some j, b) : AuxiliaryPeripheralIndex k) ≠ (some j, c) := by
      intro heq
      exact hbc (congrArg Prod.snd heq)
    exact hnc (some j, b) (some j, c) hne p q hp hq t
  have hcycN : ∀ b,
      Elementary.elementaryClosure (gN b) = Subgroup.zpowers (gN b) :=
    fun b => hcyc (none, b)
  have hcycS : ∀ j b,
      Elementary.elementaryClosure (gS j b) = Subgroup.zpowers (gS j b) :=
    fun j b => hcyc (some j, b)
  have hembN : (coneOffFamily A.alphabet
      (fun b => Subgroup.zpowers (gN b))).IsHyperbolicallyEmbedded :=
    isHyperbolicallyEmbedded_zpowers_of_elementaryClosure_eq_unconditional
      A gN hncN hloxN hcycN
  have hembS : ∀ j, (coneOffFamily A.alphabet
      (fun b => Subgroup.zpowers (gS j b))).IsHyperbolicallyEmbedded := by
    intro j
    exact isHyperbolicallyEmbedded_zpowers_of_elementaryClosure_eq_unconditional
      A (gS j) (hncS j) (hloxS j) (hcycS j)
  let EN : HypEmbeddedCore₂ A N := HypEmbeddedCore₂.ofConeOff
    (fun b => Subgroup.zpowers (gN b))
    (fun b => Subgroup.zpowers_le.mpr (hgN b)) hembN gN
    (fun b => Subgroup.mem_zpowers (gN b)) hloxN
    (fun x hx₀ hx₁ => eq_one_of_mem_zpowers_of_notCommensurable
      (fun c p q hp hq => by
        simpa only [inv_inv] using
          hncN false true Bool.false_ne_true p q hp hq c⁻¹)
      hx₀ hx₁)
  let ES : ∀ j, HypEmbeddedCore₂ A (S j) := fun j => HypEmbeddedCore₂.ofConeOff
    (fun b => Subgroup.zpowers (gS j b))
    (fun b => Subgroup.zpowers_le.mpr (hgS j b)) (hembS j) (gS j)
    (fun b => Subgroup.mem_zpowers (gS j b)) (hloxS j)
    (fun x hx₀ hx₁ => eq_one_of_mem_zpowers_of_notCommensurable
      (fun c p q hp hq => by
        simpa only [inv_inv] using
          hncS j false true Bool.false_ne_true p q hp hq c⁻¹)
      hx₀ hx₁)
  let C : AuxiliaryNonElementaryCores A N S :=
    { coreN := EN
      coreS := ES
      cyclicN := by intro b; rfl
      cyclicS := by intro j b; rfl }
  have hembAll : (coneOffFamily A.alphabet
      (fun i => Subgroup.zpowers (g i))).IsHyperbolicallyEmbedded :=
    isHyperbolicallyEmbedded_zpowers_of_elementaryClosure_eq_unconditional
      A g hnc hlox hcyc
  refine ⟨⟨C, coneOffFamily A.alphabet (fun i => Subgroup.zpowers (g i)),
    rfl, ?_, hembAll⟩⟩
  rintro ⟨i, b⟩
  cases i <;> rfl

/-- Hull's printed all-`m` `yi` statement is now the only selection premise:
finite avoidance performs the simultaneous choice, and Theorem 3.16 supplies
the whole embedded family. -/
theorem simultaneousAuxiliaryPeripheralSelection_of_finiteYi_theorem316
    (hyi : YiSuitableFiniteFamily.{u}) :
    SimultaneousAuxiliaryPeripheralSelection.{u} :=
  simultaneousAuxiliaryPeripheralSelection_of_yi_theorem316
    (simultaneousYiSuitableFamily_of_finiteFamily hyi)

end HullSC
end GroupApproximation
