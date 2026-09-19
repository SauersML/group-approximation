import GroupApproximation.Monsters.ExplicitLinearModelScaling
import GroupApproximation.Sofic.LiteralNonMFLinearWitness
import GroupApproximation.Sofic.ScalingFamilyPresentation

/-!
# Exact linear/Clifford witness for the scaling family

`LiteralNonMFLinearWitness` feeds conjugation by `D = diag(2,2,2,1)` into the
generic telescope/Clifford construction and reads the marked word off as the
nontrivial Clifford sign.  Nothing in that argument uses the exponent `2`:
the twenty base relations are the same rational affine identities for every
`m`, the stable relations are exactly the statement that conjugation by
`D_m = diag(m,m,m,1)` raises each translation generator to the `m`-th power,
and the site separation needed for the Clifford anticommutation is the
escape of `v₁` from the conjugated copy, which holds for every `m ≥ 2`
because `D_m⁻¹ v₁ D_m` has the entry `1/m`.

This file therefore reruns the witness with `conjScale m` in place of
`conjD`, giving `mark m ≠ 1` for every `m ≥ 2`.  The six affine generators
and their twenty relations are imported unchanged from the literal witness.
-/

namespace GroupApproximation
namespace ScalingFamilyLinearWitness

open LiteralNonMFPresentation ExplicitLinearModel ExplicitLinearModelScaling
open LiteralNonMFLinearWitness
open MarkedCompression

noncomputable section

variable {m : ℕ}

/-- The scaling exponents used here are nonzero. -/
theorem ne_zero_of_two_le (hm : 2 ≤ m) : m ≠ 0 := by omega

/-! ## The scaled telescope/Clifford target -/

/-- Conjugation by `D_m` as the compressing endomorphism. -/
abbrev alphaScale (hm : 2 ≤ m) : gammaBar →* gammaBar :=
  conjScale m (ne_zero_of_two_le hm)

theorem alphaScale_injective (hm : 2 ≤ m) :
    Function.Injective (alphaScale hm) :=
  conjScale_injective (ne_zero_of_two_le hm)

/-- The marked generator escapes the `m`-scaled copy. -/
theorem v1G_not_mem_range_alphaScale (hm : 2 ≤ m) :
    v1G ∉ Set.range (alphaScale hm) :=
  v1G_not_mem_range_conjScale (ne_zero_of_two_le hm) hm

/-- The affine--Clifford ambient group of the `m`-th member. -/
abbrev WitnessGroup (hm : 2 ≤ m) : Type :=
  Ambient (alphaScale hm) (alphaScale_injective hm)

/-- Images of the six base letters in the `m`-th Clifford ambient group. -/
def witnessBaseGenerator (hm : 2 ≤ m) (i : BaseGenerator) : WitnessGroup hm :=
  iotaAmbient (alphaScale hm) (alphaScale_injective hm) (matrixBaseGenerator i)

/-- Free evaluation commutes with the base homomorphism into the ambient
group. -/
theorem witness_eval_base (hm : 2 ≤ m) (q : FreeGroup BaseGenerator) :
    FreeGroup.lift (witnessBaseGenerator hm) q =
      iotaAmbient (alphaScale hm) (alphaScale_injective hm)
        (FreeGroup.lift matrixBaseGenerator q) := by
  change (FreeGroup.lift (witnessBaseGenerator hm)) q =
    ((iotaAmbient (alphaScale hm) (alphaScale_injective hm)).comp
      (FreeGroup.lift matrixBaseGenerator)) q
  apply freeGroup_hom_eq_on_generators
  intro i
  simp [witnessBaseGenerator]

theorem witnessBaseGenerator_kills (hm : 2 ≤ m) :
    ∀ r ∈ baseRelators, FreeGroup.lift (witnessBaseGenerator hm) r = 1 := by
  intro r hr
  rw [witness_eval_base, matrixBaseGenerator_kills r hr, map_one]

/-! ## The scaled stable relations -/

/-- Conjugation by `D_m` on each of the six exact affine generators is the
`m`-th displayed compression word. -/
theorem conjScale_matrixBaseGenerator (hm : 2 ≤ m) (i : BaseGenerator) :
    alphaScale hm (matrixBaseGenerator i) =
      FreeGroup.lift matrixBaseGenerator
        (ScalingFamilyPresentation.compressedBaseWord m i) := by
  have h0 : m ≠ 0 := ne_zero_of_two_le hm
  fin_cases i
  · simpa [matrixBaseGenerator, ScalingFamilyPresentation.compressedBaseWord,
      v1Index] using conjScale_v1G (m := m) h0
  · simpa [matrixBaseGenerator, ScalingFamilyPresentation.compressedBaseWord,
      v1Index, v2Index] using conjScale_v2G (m := m) h0
  · simpa [matrixBaseGenerator, ScalingFamilyPresentation.compressedBaseWord,
      v1Index, v2Index, v3Index] using conjScale_v3G (m := m) h0
  · simpa [matrixBaseGenerator, ScalingFamilyPresentation.compressedBaseWord,
      v1Index, v2Index, v3Index, xIndex] using conjScale_xG (m := m) h0
  · simpa [matrixBaseGenerator, ScalingFamilyPresentation.compressedBaseWord,
      v1Index, v2Index, v3Index, xIndex, yIndex] using conjScale_yG (m := m) h0
  · simpa [matrixBaseGenerator, ScalingFamilyPresentation.compressedBaseWord,
      v1Index, v2Index, v3Index, xIndex, yIndex, zIndex] using
      conjScale_zG (m := m) h0

/-- The exact target data for every relation of the `m`-th presentation. -/
noncomputable def realization (hm : 2 ≤ m) :
    ScalingFamilyPresentation.Realization m (WitnessGroup hm) where
  baseGenerator := witnessBaseGenerator hm
  stable := tAmbient (alphaScale hm) (alphaScale_injective hm)
  lamp := cAmbient (alphaScale hm) (alphaScale_injective hm)
  base_relations := witnessBaseGenerator_kills hm
  stable_relations i := by
    simp only [witnessBaseGenerator]
    rw [compress]
    rw [show alphaScale hm (matrixBaseGenerator i) =
      FreeGroup.lift matrixBaseGenerator
        (ScalingFamilyPresentation.compressedBaseWord m i) from
      conjScale_matrixBaseGenerator hm i]
    symm
    exact witness_eval_base hm (ScalingFamilyPresentation.compressedBaseWord m i)
  lamp_sq := cAmbient_sq (alphaScale hm) (alphaScale_injective hm)
  lamp_centralizes_base i := comm_c (alphaScale hm) (alphaScale_injective hm) _
  marked_central g := by
    simp only [witnessBaseGenerator, matrixBaseGenerator_v1]
    rw [marked_word_eq_sign (alphaScale hm) (alphaScale_injective hm)
      (v1G_not_mem_range_alphaScale hm)]
    exact signAmbient_central (alphaScale hm) (alphaScale_injective hm) g

theorem realization_marked_word (hm : 2 ≤ m) :
    markedCompressionWord (realization hm).stable
      ((realization hm).baseGenerator v1Index) (realization hm).lamp =
        signAmbient (alphaScale hm) (alphaScale_injective hm) := by
  simp only [realization, witnessBaseGenerator, matrixBaseGenerator_v1]
  exact marked_word_eq_sign (alphaScale hm) (alphaScale_injective hm)
    (v1G_not_mem_range_alphaScale hm)

/-- The homomorphism from the `m`-th presentation to its explicit
affine--Clifford witness. -/
noncomputable def witnessHom (hm : 2 ≤ m) :
    ScalingFamilyPresentation.MarkedGroup m →* WitnessGroup hm :=
  ScalingFamilyPresentation.realizationHom (realization hm)

/-- The `m`-th marked word maps exactly to the nontrivial central Clifford
sign in the witness group. -/
@[simp] theorem witnessHom_mark (hm : 2 ≤ m) :
    witnessHom hm (ScalingFamilyPresentation.mark m) =
      signAmbient (alphaScale hm) (alphaScale_injective hm) := by
  rw [witnessHom, ScalingFamilyPresentation.realizationHom_mark,
    realization_marked_word]

/-- **Exact separation of the marked involution for every scaling factor.** -/
theorem scaling_mark_ne_one (hm : 2 ≤ m) :
    ScalingFamilyPresentation.mark m ≠ 1 := by
  apply ScalingFamilyPresentation.mark_ne_one_of_realization (realization hm)
  rw [realization_marked_word]
  exact signAmbient_ne_one (alphaScale hm) (alphaScale_injective hm)

/-- At `m = 2` this is the literal manuscript separation. -/
theorem scaling_mark_ne_one_two : ScalingFamilyPresentation.mark 2 ≠ 1 :=
  scaling_mark_ne_one (le_refl 2)

/-- The exact algebraic package for the `m`-th member of the family. -/
theorem scaling_finitelyPresented_nontrivial_mark (hm : 2 ≤ m) :
    Group.IsFinitelyPresented (ScalingFamilyPresentation.MarkedGroup m) ∧
      ScalingFamilyPresentation.mark m ^ 2 = 1 ∧
      (∀ g : ScalingFamilyPresentation.MarkedGroup m,
        Commute (ScalingFamilyPresentation.mark m) g) ∧
      ScalingFamilyPresentation.mark m ≠ 1 :=
  ⟨inferInstance, ScalingFamilyPresentation.mark_sq m,
    ScalingFamilyPresentation.mark_central m, scaling_mark_ne_one hm⟩

end

end ScalingFamilyLinearWitness
end GroupApproximation
