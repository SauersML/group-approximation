import GroupApproximation.Monsters.CyclicBaseCalibration
import GroupApproximation.Sofic.OperatorMF
import GroupApproximation.Sofic.OperatorMFPositiveControls
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.PresentedGroup

/-!
# The literal cyclic-base calibration

This file formalizes the three-generator presentation printed in Theorem C
of the manuscript.  It maps that presentation to the existing exact Clifford
cyclic model, where the marked central involution survives, and proves that
every finite-dimensional linear representation kills the marked element.

No amenability-to-MF theorem is assumed or postulated here.  The final corona
statement takes operator-MF of the concrete Clifford target as an explicit
hypothesis.
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

/-! ## Finite-dimensional kill and the conditional MF calibration -/

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

/-- The realized Clifford quotient is operator-MF whenever the ambient
Clifford cyclic model is.  The manuscript supplies the premise from
amenability and quasidiagonality; Lean records only the formal subgroup
permanence step here. -/
theorem realizedQuotient_isOperatorMF
    (hMF : IsOperatorMF CliffordBS) : IsOperatorMF RealizedQuotient :=
  hMF.subgroup realization.range

/-- If the concrete Clifford cyclic target is operator-MF, the literal group
has a standard corona representation in which its marked involution survives.
This keeps the paper-side amenability/TWW input explicit. -/
theorem exists_coronaRepresentation_mark_ne_one
    (hMF : IsOperatorMF CliffordBS) :
    ∃ (X : ℕ → FiniteModel), (∀ n, 0 < Fintype.card (X n)) ∧
      ∃ rho : LiteralGroup →* NormMatrixCoronaUnitary X, rho mark ≠ 1 := by
  obtain ⟨X, hX, rho, hrho⟩ := hMF
  refine ⟨X, hX, rho.comp realization, ?_⟩
  intro h
  apply markedWord_ne_one
  apply hrho
  simpa [MonoidHom.comp_apply, realization_mark] using h

end
end LiteralCyclicCalibration
end GroupApproximation
