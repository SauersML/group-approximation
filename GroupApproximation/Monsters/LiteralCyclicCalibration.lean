import GroupApproximation.Monsters.CyclicBaseCalibration
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.PresentedGroup

/-!
# The literal cyclic-base calibration

This file formalizes the three-generator presentation printed in Theorem C
of the manuscript.  It maps that presentation to the existing exact Clifford
cyclic model, where the marked central involution survives, and proves that
every finite-dimensional linear representation kills the marked element.

This module makes no analytic MF or corona-survival claim.
-/

namespace GroupApproximation
namespace LiteralCyclicCalibration

open scoped commutatorElement
open CyclicBaseCalibration

noncomputable section

/-! ## The literal presentation -/

/-- The letters `γ₀`, `t`, and `c`. -/
abbrev Generator := Fin 3

local instance : DecidableEq (FreeGroup Generator) := Classical.decEq _

abbrev gammaIndex : Generator := 0
abbrev stableIndex : Generator := 1
abbrev lampIndex : Generator := 2

abbrev gammaWord : FreeGroup Generator := FreeGroup.of gammaIndex
abbrev stableWord : FreeGroup Generator := FreeGroup.of stableIndex
abbrev lampWord : FreeGroup Generator := FreeGroup.of lampIndex

/-- Raw commutator word, with convention `[g,h]=ghg⁻¹h⁻¹`. -/
def commutatorWord {H : Type*} [Group H] (g h : H) : H :=
  g * h * g⁻¹ * h⁻¹

abbrev displacedLampWord : FreeGroup Generator :=
  stableWord * lampWord * stableWord⁻¹

/-- The literal marked word `w_BS`. -/
abbrev markedWord : FreeGroup Generator :=
  commutatorWord displacedLampWord
    (gammaWord * displacedLampWord * gammaWord⁻¹)

abbrev stableRelator : FreeGroup Generator :=
  stableWord * gammaWord * stableWord⁻¹ * (gammaWord ^ 2)⁻¹

abbrev lampSqRelator : FreeGroup Generator := lampWord ^ 2
abbrev lampGammaRelator : FreeGroup Generator :=
  commutatorWord lampWord gammaWord
abbrev markedSqRelator : FreeGroup Generator := markedWord ^ 2
abbrev markedGammaRelator : FreeGroup Generator :=
  commutatorWord markedWord gammaWord
abbrev markedStableRelator : FreeGroup Generator :=
  commutatorWord markedWord stableWord
abbrev markedLampRelator : FreeGroup Generator :=
  commutatorWord markedWord lampWord

/-- Exactly the seven relators in the manuscript's presentation of
`E_BS`. -/
noncomputable def relators : Finset (FreeGroup Generator) :=
  [stableRelator, lampSqRelator, lampGammaRelator, markedSqRelator,
    markedGammaRelator, markedStableRelator, markedLampRelator].toFinset

noncomputable abbrev LiteralGroup : Type :=
  PresentedGroup ((relators : Finset (FreeGroup Generator)) :
    Set (FreeGroup Generator))

instance literalGroup_finitelyPresented : Group.IsFinitelyPresented LiteralGroup :=
  inferInstance

noncomputable instance literalGroup_countable : Countable LiteralGroup :=
  by
    letI : Countable (FreeGroup Generator) := by
      have hfree : Function.Surjective
          (FreeGroup.mk : List (Generator × Bool) → FreeGroup Generator) := by
        intro g
        obtain ⟨L, hL⟩ := Quot.exists_rep g
        exact ⟨L, by rw [← FreeGroup.quot_mk_eq_mk, hL]⟩
      exact hfree.countable
    exact (PresentedGroup.mk_surjective
      ((relators : Finset (FreeGroup Generator)) :
        Set (FreeGroup Generator))).countable

noncomputable abbrev evalWord : FreeGroup Generator →* LiteralGroup :=
  PresentedGroup.mk _

noncomputable abbrev gamma : LiteralGroup := evalWord gammaWord
noncomputable abbrev stable : LiteralGroup := evalWord stableWord
noncomputable abbrev lamp : LiteralGroup := evalWord lampWord
noncomputable abbrev mark : LiteralGroup := evalWord markedWord

theorem stable_relation : stable * gamma * stable⁻¹ = gamma ^ 2 := by
  apply mul_inv_eq_one.mp
  change evalWord stableRelator = 1
  apply PresentedGroup.one_of_mem
  simp [relators]

theorem lamp_sq : lamp ^ 2 = 1 := by
  change evalWord lampSqRelator = 1
  apply PresentedGroup.one_of_mem
  simp [relators]

theorem lamp_comm_gamma : Commute lamp gamma := by
  apply commutatorElement_eq_one_iff_commute.mp
  change evalWord lampGammaRelator = 1
  apply PresentedGroup.one_of_mem
  simp [relators]

theorem mark_eq_markedCompressionWord :
    mark = markedCompressionWord stable gamma lamp := by
  simp [mark, markedWord, displacedLampWord, commutatorWord,
    markedCompressionWord, commutatorElement_def]

theorem mark_sq : mark ^ 2 = 1 := by
  change evalWord markedSqRelator = 1
  apply PresentedGroup.one_of_mem
  simp [relators]

theorem mark_comm_gamma : Commute mark gamma := by
  apply commutatorElement_eq_one_iff_commute.mp
  change evalWord markedGammaRelator = 1
  apply PresentedGroup.one_of_mem
  simp [relators]

theorem mark_comm_stable : Commute mark stable := by
  apply commutatorElement_eq_one_iff_commute.mp
  change evalWord markedStableRelator = 1
  apply PresentedGroup.one_of_mem
  simp [relators]

theorem mark_comm_lamp : Commute mark lamp := by
  apply commutatorElement_eq_one_iff_commute.mp
  change evalWord markedLampRelator = 1
  apply PresentedGroup.one_of_mem
  simp [relators]

/-- The three displayed commutation relators make the marked element central
in the whole literal presented group. -/
theorem mark_central (g : LiteralGroup) : Commute mark g := by
  have hgen : ∀ i : Generator,
      Commute mark (evalWord (FreeGroup.of i)) := by
    intro i
    fin_cases i
    · exact mark_comm_gamma
    · exact mark_comm_stable
    · exact mark_comm_lamp
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ g
  induction w using FreeGroup.induction_on with
  | C1 => exact Commute.one_right _
  | of i => exact hgen i
  | inv_of i hi =>
      rw [map_inv]
      exact hi.inv_right
  | mul a b ha hb =>
      simpa only [map_mul] using ha.mul_right hb

/-! ## Exact realization in the Clifford cyclic model -/

noncomputable def targetGenerator : Generator → CliffordBS
  | 0 => gammaBS
  | 1 => tBS
  | 2 => cBS

@[simp] theorem targetGenerator_gamma : targetGenerator gammaIndex = gammaBS := rfl
@[simp] theorem targetGenerator_stable : targetGenerator stableIndex = tBS := rfl
@[simp] theorem targetGenerator_lamp : targetGenerator lampIndex = cBS := rfl

/-- Evaluation of a represented word under the universal map out of a
presented group. -/
@[simp] theorem presentedToGroup_mk {H : Type*} [Group H]
    {R : Set (FreeGroup Generator)} {f : Generator → H}
    (h : ∀ r ∈ R, FreeGroup.lift f r = 1)
    (w : FreeGroup Generator) :
    PresentedGroup.toGroup h (PresentedGroup.mk R w) =
      FreeGroup.lift f w := rfl

theorem target_eval_marked :
    FreeGroup.lift targetGenerator markedWord =
      markedCompressionWord tBS gammaBS cBS := by
  simp [markedWord, displacedLampWord, commutatorWord,
    markedCompressionWord, commutatorElement_def]

theorem target_kills_relators :
    ∀ r ∈ relators, FreeGroup.lift targetGenerator r = 1 := by
  intro r hr
  simp [relators] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [stableRelator, stableWord, gammaWord, map_mul, map_inv,
      map_pow, FreeGroup.lift_apply_of, targetGenerator_stable,
      targetGenerator_gamma] using mul_inv_eq_one.mpr tBS_conj_gammaBS
  · simp only [lampSqRelator, lampWord, map_pow, FreeGroup.lift_apply_of,
      targetGenerator_lamp]
    rw [cBS, ← map_pow, CliffordAlgebraLamp.lampGen_sq, map_one]
  · simpa only [lampGammaRelator, lampWord, gammaWord, commutatorWord,
      commutatorElement_def, map_mul, map_inv, FreeGroup.lift_apply_of,
      targetGenerator_lamp, targetGenerator_gamma] using
        commutatorElement_eq_one_iff_commute.mpr cBS_comm_gammaBS
  · simpa only [markedSqRelator, markedWord, displacedLampWord,
      commutatorWord, markedCompressionWord, commutatorElement_def,
      stableWord, lampWord, gammaWord, map_mul, map_inv, map_pow,
      FreeGroup.lift_apply_of, targetGenerator_stable,
      targetGenerator_lamp, targetGenerator_gamma] using markedWord_sq
  · simpa only [markedGammaRelator, markedWord, displacedLampWord,
      commutatorWord, markedCompressionWord, commutatorElement_def,
      stableWord, lampWord, gammaWord, map_mul, map_inv,
      FreeGroup.lift_apply_of, targetGenerator_stable,
      targetGenerator_lamp, targetGenerator_gamma] using
        commutatorElement_eq_one_iff_commute.mpr
          (markedWord_central gammaBS)
  · simpa only [markedStableRelator, markedWord, displacedLampWord,
      commutatorWord, markedCompressionWord, commutatorElement_def,
      stableWord, lampWord, gammaWord, map_mul, map_inv,
      FreeGroup.lift_apply_of, targetGenerator_stable,
      targetGenerator_lamp, targetGenerator_gamma] using
        commutatorElement_eq_one_iff_commute.mpr
          (markedWord_central tBS)
  · simpa only [markedLampRelator, markedWord, displacedLampWord,
      commutatorWord, markedCompressionWord, commutatorElement_def,
      stableWord, lampWord, gammaWord, map_mul, map_inv,
      FreeGroup.lift_apply_of, targetGenerator_stable,
      targetGenerator_lamp, targetGenerator_gamma] using
        commutatorElement_eq_one_iff_commute.mpr
          (markedWord_central cBS)

/-- The literal presentation maps to the concrete Clifford cyclic model. -/
noncomputable def realization : LiteralGroup →* CliffordBS :=
  PresentedGroup.toGroup target_kills_relators

@[simp] theorem realization_generator (i : Generator) :
    realization (PresentedGroup.of i) = targetGenerator i :=
  PresentedGroup.toGroup.of _

theorem realization_mark :
    realization mark = markedCompressionWord tBS gammaBS cBS := by
  change PresentedGroup.toGroup _ (PresentedGroup.mk _ markedWord) = _
  rw [presentedToGroup_mk]
  exact target_eval_marked

/-- The literal marked involution survives. -/
theorem mark_ne_one : mark ≠ 1 := by
  intro h
  apply markedWord_ne_one
  rw [← realization_mark, h, map_one]

/-- The honest quotient target generated by the three displayed images.
The ambient `CliffordBS` model is deliberately larger; this range is the
literal quotient realized inside it. -/
abbrev RealizedQuotient : Type := realization.range

noncomputable def quotientMap : LiteralGroup →* RealizedQuotient :=
  realization.rangeRestrict

theorem quotientMap_surjective : Function.Surjective quotientMap :=
  realization.rangeRestrict_surjective

theorem quotientMap_mark_ne_one : quotientMap mark ≠ 1 := by
  intro h
  apply markedWord_ne_one
  have hv := congrArg Subtype.val h
  simpa [quotientMap, realization_mark] using hv

/-- The literal marked word maps to the distinguished Clifford sign, not
merely to some unspecified nontrivial element of the realized quotient. -/
theorem quotientMap_mark_val :
    ((quotientMap mark : RealizedQuotient) : CliffordBS) = zBS := by
  change realization mark = zBS
  rw [realization_mark, markedWord_eq_zBS]

/-- The surviving image of the literal mark is still an involution. -/
theorem quotientMap_mark_sq : quotientMap mark ^ 2 = 1 := by
  rw [← map_pow, mark_sq, map_one]

/-- The surviving image of the literal mark is central in the realized
quotient, because its value is the central Clifford sign. -/
theorem quotientMap_mark_central (g : RealizedQuotient) :
    Commute (quotientMap mark) g := by
  apply Subtype.ext
  change ((quotientMap mark : RealizedQuotient) : CliffordBS) *
      (g : CliffordBS) =
    (g : CliffordBS) * ((quotientMap mark : RealizedQuotient) : CliffordBS)
  rw [quotientMap_mark_val]
  exact (zBS_central (g : CliffordBS)).eq

/-- The concrete quotient generated by the three displayed elements is
finitely generated.  This is the exact quotient realized by the literal
finite presentation; no presentation-completeness assertion is hidden here. -/
theorem realizedQuotient_finitelyGenerated : Group.FG RealizedQuotient := by
  letI : Group.FG LiteralGroup :=
    Group.fg_of_surjective
      (PresentedGroup.mk_surjective
        ((relators : Finset (FreeGroup Generator)) :
          Set (FreeGroup Generator)))
  exact Group.fg_of_surjective quotientMap_surjective

/-! ## Finite-dimensional kill -/

def cyclicBase : Set LiteralGroup := {g | ∃ n : ℤ, g = gamma ^ n}

theorem gamma_mem_cyclicBase : gamma ∈ cyclicBase :=
  ⟨1, (pow_one gamma).symm⟩

theorem stable_compresses_cyclicBase :
    ∀ g ∈ cyclicBase, stable * g * stable⁻¹ ∈ cyclicBase := by
  rintro g ⟨n, rfl⟩
  refine ⟨2 * n, ?_⟩
  rw [← conj_zpow, stable_relation]
  exact (zpow_mul gamma 2 n).symm

theorem lamp_centralizes_cyclicBase :
    ∀ g ∈ cyclicBase, lamp * g = g * lamp := by
  rintro g ⟨n, rfl⟩
  exact (lamp_comm_gamma.zpow_right n).eq

/-- Every finite-dimensional representation of the literal group, over every
field, kills its nontrivial marked element. -/
theorem finiteDimensional_kill
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (pi : LiteralGroup →* (Module.End k V)ˣ) :
    pi mark = 1 := by
  rw [mark_eq_markedCompressionWord]
  simpa [markedCompressionWord] using
    map_marked_commutator_eq_one_units pi gamma_mem_cyclicBase
      stable_compresses_cyclicBase lamp_centralizes_cyclicBase

/-- Every finite-dimensional representation of the realized Clifford
quotient kills the image of the marked element.  This is the quotient-side
half of the "either group" assertion in manuscript Theorem C. -/
theorem realizedQuotient_finiteDimensional_kill
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (pi : RealizedQuotient →* (Module.End k V)ˣ) :
    pi (quotientMap mark) = 1 := by
  simpa using finiteDimensional_kill (pi.comp quotientMap)

/-- Exact outer-form package for the manuscript's cyclic-base comparison.
It deliberately stops at the algebraic calibration: finite presentation,
survival of the marked word in the explicit realized quotient, and its
annihilation by every finite-dimensional representation over every field. -/
theorem manuscriptCyclicCalibration :
    Fintype.card Generator = 3 ∧
      (gammaIndex = 0 ∧ stableIndex = 1 ∧ lampIndex = 2) ∧
      stableRelator =
        stableWord * gammaWord * stableWord⁻¹ * (gammaWord ^ 2)⁻¹ ∧
      lampSqRelator = lampWord ^ 2 ∧
      lampGammaRelator =
        lampWord * gammaWord * lampWord⁻¹ * gammaWord⁻¹ ∧
      markedSqRelator = markedWord ^ 2 ∧
      markedGammaRelator =
        markedWord * gammaWord * markedWord⁻¹ * gammaWord⁻¹ ∧
      markedStableRelator =
        markedWord * stableWord * markedWord⁻¹ * stableWord⁻¹ ∧
      markedLampRelator =
        markedWord * lampWord * markedWord⁻¹ * lampWord⁻¹ ∧
      relators =
        [stableRelator, lampSqRelator, lampGammaRelator, markedSqRelator,
          markedGammaRelator, markedStableRelator,
          markedLampRelator].toFinset ∧
      markedWord =
        (let displaced := stableWord * lampWord * stableWord⁻¹
         displaced * (gammaWord * displaced * gammaWord⁻¹) * displaced⁻¹ *
          (gammaWord * displaced * gammaWord⁻¹)⁻¹) ∧
      Group.IsFinitelyPresented LiteralGroup ∧
      mark ≠ 1 ∧
      Function.Surjective quotientMap ∧
      quotientMap mark ≠ 1 ∧
      (((quotientMap mark : RealizedQuotient) : CliffordBS) = zBS) ∧
      (∀ g : RealizedQuotient, Commute (quotientMap mark) g) ∧
      (∀ {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
        [FiniteDimensional k V]
        (pi : LiteralGroup →* (Module.End k V)ˣ), pi mark = 1) := by
  exact ⟨by decide, ⟨rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, inferInstance, mark_ne_one, quotientMap_surjective,
    quotientMap_mark_ne_one, quotientMap_mark_val,
    quotientMap_mark_central,
    by
      intro k V _ _ _ _ pi
      exact finiteDimensional_kill pi⟩

end
end LiteralCyclicCalibration
end GroupApproximation
