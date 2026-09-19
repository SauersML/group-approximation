import GroupApproximation.Monsters.ExplicitLinearModel
import GroupApproximation.Sofic.LiteralNonMFPresentation
import GroupApproximation.Sofic.MarkedCompressionGroup

/-!
# Exact linear/Clifford witness for the literal presentation

The rational affine matrices in `ExplicitLinearModel` satisfy every one of
the twenty literal base relations.  Conjugation by the doubling matrix gives
the six stable-letter relations, and its integrality invariant separates
`v1` from the compression range.  Feeding that exact data into the generic
telescope/Clifford construction produces a homomorphism from the literal
eight-generator presented group whose marked word is the nontrivial Clifford
sign.

This proves consistency and `mark != 1` without using completeness of the
CRW presentation and without using property `(T)`.
-/

namespace GroupApproximation
namespace LiteralNonMFLinearWitness

open LiteralNonMFPresentation ExplicitLinearModel
open MarkedCompression

noncomputable section

/-! ## Evaluation of the six base letters -/

/-- The literal base alphabet evaluated in the affine rational matrix group. -/
def matrixBaseGenerator (i : BaseGenerator) : gammaBar :=
  if i = v1Index then v1G
  else if i = v2Index then v2G
  else if i = v3Index then v3G
  else if i = xIndex then xG
  else if i = yIndex then yG
  else zG

@[simp] theorem matrixBaseGenerator_v1 : matrixBaseGenerator v1Index = v1G := by
  simp [matrixBaseGenerator]

@[simp] theorem matrixBaseGenerator_v2 : matrixBaseGenerator v2Index = v2G := by
  simp [matrixBaseGenerator, v1Index, v2Index]

@[simp] theorem matrixBaseGenerator_v3 : matrixBaseGenerator v3Index = v3G := by
  simp [matrixBaseGenerator, v1Index, v2Index, v3Index]

@[simp] theorem matrixBaseGenerator_x : matrixBaseGenerator xIndex = xG := by
  simp [matrixBaseGenerator, v1Index, v2Index, v3Index, xIndex]

@[simp] theorem matrixBaseGenerator_y : matrixBaseGenerator yIndex = yG := by
  simp [matrixBaseGenerator, v1Index, v2Index, v3Index, xIndex, yIndex]

@[simp] theorem matrixBaseGenerator_z : matrixBaseGenerator zIndex = zG := by
  simp [matrixBaseGenerator, v1Index, v2Index, v3Index, xIndex, yIndex, zIndex]

/-- The twenty base relations are verified in separate declarations.  Each
proof reuses the named exact matrix identity from `ExplicitLinearModel`;
in particular, elaboration never unfolds a large free-group expression into
sixteen independent scalar normalization problems. -/
theorem matrix_kills_xCube :
    FreeGroup.lift matrixBaseGenerator baseRelXCube = 1 := by
  simp only [map_pow, FreeGroup.lift_apply_of, matrixBaseGenerator_x]
  apply Subtype.ext
  apply Units.ext
  simpa [pow_succ, xG, xU] using xM_orderThree'
theorem matrix_kills_yCube :
    FreeGroup.lift matrixBaseGenerator baseRelYCube = 1 := by
  simp only [map_pow, FreeGroup.lift_apply_of, matrixBaseGenerator_y]
  apply Subtype.ext
  apply Units.ext
  simpa [pow_succ, yG, yU] using yM_orderThree'
theorem matrix_kills_zSq :
    FreeGroup.lift matrixBaseGenerator baseRelZSq = 1 := by
  simp only [map_pow, FreeGroup.lift_apply_of, matrixBaseGenerator_z]
  apply Subtype.ext
  apply Units.ext
  simpa [pow_succ, zG, zU] using zM_orderTwo
theorem matrix_kills_xzCube :
    FreeGroup.lift matrixBaseGenerator baseRelXZCube = 1 := by
  simp only [map_pow, map_mul, FreeGroup.lift_apply_of,
    matrixBaseGenerator_x, matrixBaseGenerator_z]
  apply Subtype.ext
  apply Units.ext
  simpa [pow_succ, xG, zG, xU, zU] using rel_xz_cube
theorem matrix_kills_yzCube :
    FreeGroup.lift matrixBaseGenerator baseRelYZCube = 1 := by
  simp only [map_pow, map_mul, FreeGroup.lift_apply_of,
    matrixBaseGenerator_y, matrixBaseGenerator_z]
  apply Subtype.ext
  apply Units.ext
  simpa [pow_succ, yG, zG, yU, zU] using rel_yz_cube
theorem matrix_kills_xInvZxy :
    FreeGroup.lift matrixBaseGenerator baseRelXInvZXY = 1 := by
  simp only [map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
    matrixBaseGenerator_x, matrixBaseGenerator_y, matrixBaseGenerator_z]
  apply Subtype.ext
  apply Units.ext
  simpa [pow_succ, xG, yG, zG, xU, yU, zU] using rel_xzxy_sq
theorem matrix_kills_yInvZyx :
    FreeGroup.lift matrixBaseGenerator baseRelYInvZYX = 1 := by
  simp only [map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
    matrixBaseGenerator_x, matrixBaseGenerator_y, matrixBaseGenerator_z]
  apply Subtype.ext
  apply Units.ext
  simpa [pow_succ, xG, yG, zG, xU, yU, zU] using rel_yzyx_sq
theorem matrix_kills_xySix :
    FreeGroup.lift matrixBaseGenerator baseRelXYSix = 1 := by
  simp only [map_pow, map_mul, FreeGroup.lift_apply_of,
    matrixBaseGenerator_x, matrixBaseGenerator_y]
  rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add]
  apply Subtype.ext
  apply Units.ext
  change (xM * yM) ^ 3 * (xM * yM) ^ 3 = 1
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using rel_xy_six
theorem matrix_kills_v12 :
    FreeGroup.lift matrixBaseGenerator baseRelV12 = 1 := by
  rw [map_commutatorWord]
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  simp only [FreeGroup.lift_apply_of, matrixBaseGenerator_v1,
    matrixBaseGenerator_v2]
  apply Subtype.ext
  apply Units.ext
  simpa [v1G, v2G, v1U, v2U] using rel_v12
theorem matrix_kills_v13 :
    FreeGroup.lift matrixBaseGenerator baseRelV13 = 1 := by
  rw [map_commutatorWord]
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  simp only [FreeGroup.lift_apply_of, matrixBaseGenerator_v1,
    matrixBaseGenerator_v3]
  apply Subtype.ext
  apply Units.ext
  simpa [v1G, v3G, v1U, v3U] using rel_v13
theorem matrix_kills_v23 :
    FreeGroup.lift matrixBaseGenerator baseRelV23 = 1 := by
  rw [map_commutatorWord]
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  simp only [FreeGroup.lift_apply_of, matrixBaseGenerator_v2,
    matrixBaseGenerator_v3]
  apply Subtype.ext
  apply Units.ext
  simpa [v2G, v3G, v2U, v3U] using rel_v23
theorem matrix_kills_xv1 :
    FreeGroup.lift matrixBaseGenerator baseRelXV1 = 1 := by
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of,
    matrixBaseGenerator_x, matrixBaseGenerator_v1, matrixBaseGenerator_v3]
  have h : xG * v1G = v3G * xG := by
    apply Subtype.ext
    apply Units.ext
    simpa [xG, v1G, v3G, xU, v1U, v3U] using rel_x_v1
  rw [h]
  group
theorem matrix_kills_xv2 :
    FreeGroup.lift matrixBaseGenerator baseRelXV2 = 1 := by
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of,
    matrixBaseGenerator_x, matrixBaseGenerator_v1, matrixBaseGenerator_v2]
  have h : xG * v2G = v1G * xG := by
    apply Subtype.ext
    apply Units.ext
    simpa [xG, v1G, v2G, xU, v1U, v2U] using rel_x_v2
  rw [h]
  group
theorem matrix_kills_xv3 :
    FreeGroup.lift matrixBaseGenerator baseRelXV3 = 1 := by
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of,
    matrixBaseGenerator_x, matrixBaseGenerator_v2, matrixBaseGenerator_v3]
  have h : xG * v3G = v2G * xG := by
    apply Subtype.ext
    apply Units.ext
    simpa [xG, v2G, v3G, xU, v2U, v3U] using rel_x_v3
  rw [h]
  group
theorem matrix_kills_yv1 :
    FreeGroup.lift matrixBaseGenerator baseRelYV1 = 1 := by
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of,
    matrixBaseGenerator_y, matrixBaseGenerator_v1]
  have h : yG * v1G = v1G * yG := by
    apply Subtype.ext
    apply Units.ext
    simpa [yG, v1G, yU, v1U] using rel_y_v1
  rw [h]
  group
theorem matrix_kills_yv2 :
    FreeGroup.lift matrixBaseGenerator baseRelYV2 = 1 := by
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of,
    matrixBaseGenerator_y, matrixBaseGenerator_v2, matrixBaseGenerator_v3]
  have h : yG * v2G = (v2G⁻¹ * v3G) * yG := by
    apply Subtype.ext
    apply Units.ext
    simpa [yG, v2G, v3G, yU, v2U, v3U] using rel_y_v2
  rw [h]
  group
theorem matrix_kills_yv3 :
    FreeGroup.lift matrixBaseGenerator baseRelYV3 = 1 := by
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of,
    matrixBaseGenerator_y, matrixBaseGenerator_v1, matrixBaseGenerator_v2,
    matrixBaseGenerator_v3]
  have h : yG * v3G = (v1G * v2G⁻¹) * yG := by
    apply Subtype.ext
    apply Units.ext
    simpa [yG, v1G, v2G, v3G, yU, v1U, v2U, v3U] using rel_y_v3
  rw [h]
  group
theorem matrix_kills_zv1 :
    FreeGroup.lift matrixBaseGenerator baseRelZV1 = 1 := by
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of,
    matrixBaseGenerator_z, matrixBaseGenerator_v1, matrixBaseGenerator_v2,
    matrixBaseGenerator_v3]
  have h : zG * v1G = (v2G * v3G⁻¹) * zG := by
    apply Subtype.ext
    apply Units.ext
    simpa [zG, v1G, v2G, v3G, zU, v1U, v2U, v3U] using rel_z_v1
  rw [h]
  group
theorem matrix_kills_zv2 :
    FreeGroup.lift matrixBaseGenerator baseRelZV2 = 1 := by
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of,
    matrixBaseGenerator_z, matrixBaseGenerator_v1, matrixBaseGenerator_v2,
    matrixBaseGenerator_v3]
  have h : zG * v2G = (v1G * v3G⁻¹) * zG := by
    apply Subtype.ext
    apply Units.ext
    simpa [zG, v1G, v2G, v3G, zU, v1U, v2U, v3U] using rel_z_v2
  rw [h]
  group
theorem matrix_kills_zv3 :
    FreeGroup.lift matrixBaseGenerator baseRelZV3 = 1 := by
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of,
    matrixBaseGenerator_z, matrixBaseGenerator_v3]
  have h : zG * v3G = v3G⁻¹ * zG := by
    apply Subtype.ext
    apply Units.ext
    simpa [zG, v3G, zU, v3U] using rel_z_v3
  rw [h]
  group

/-- All twenty displayed base relators hold in the exact affine model. -/
theorem matrixBaseGenerator_kills :
    ∀ r ∈ baseRelators, FreeGroup.lift matrixBaseGenerator r = 1 := by
  intro r hr
  rw [mem_baseRelators_iff] at hr
  rcases hr with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact matrix_kills_xCube
  · exact matrix_kills_yCube
  · exact matrix_kills_zSq
  · exact matrix_kills_xzCube
  · exact matrix_kills_yzCube
  · exact matrix_kills_xInvZxy
  · exact matrix_kills_yInvZyx
  · exact matrix_kills_xySix
  · exact matrix_kills_v12
  · exact matrix_kills_v13
  · exact matrix_kills_v23
  · exact matrix_kills_xv1
  · exact matrix_kills_xv2
  · exact matrix_kills_xv3
  · exact matrix_kills_yv1
  · exact matrix_kills_yv2
  · exact matrix_kills_yv3
  · exact matrix_kills_zv1
  · exact matrix_kills_zv2
  · exact matrix_kills_zv3

/-! ## The generic telescope/Clifford target -/

abbrev alpha : gammaBar →* gammaBar := conjD

abbrev WitnessGroup : Type := Ambient alpha conjD_injective

/-- Images of the six base letters in the Clifford ambient group. -/
def witnessBaseGenerator (i : BaseGenerator) : WitnessGroup :=
  iotaAmbient alpha conjD_injective (matrixBaseGenerator i)

/-- Free evaluation commutes with the base homomorphism into the ambient
group. -/
theorem witness_eval_base (q : FreeGroup BaseGenerator) :
    FreeGroup.lift witnessBaseGenerator q =
      iotaAmbient alpha conjD_injective
        (FreeGroup.lift matrixBaseGenerator q) := by
  change (FreeGroup.lift witnessBaseGenerator) q =
    ((iotaAmbient alpha conjD_injective).comp
      (FreeGroup.lift matrixBaseGenerator)) q
  apply freeGroup_hom_eq_on_generators
  intro i
  simp [witnessBaseGenerator]

theorem witnessBaseGenerator_kills :
    ∀ r ∈ baseRelators, FreeGroup.lift witnessBaseGenerator r = 1 := by
  intro r hr
  rw [witness_eval_base, matrixBaseGenerator_kills r hr, map_one]

/-- The unit-level doubling identity for `v₁`. -/
theorem dU_conj_v1U : dU * v1U * dU⁻¹ = v1U * v1U := by
  apply Units.ext
  change dM * v1M * dInvM = v1M * v1M
  rw [rel_d_v1, mul_assoc, dM_inv, mul_one]

/-- The unit-level doubling identity for `v₂`. -/
theorem dU_conj_v2U : dU * v2U * dU⁻¹ = v2U * v2U := by
  apply Units.ext
  change dM * v2M * dInvM = v2M * v2M
  rw [rel_d_v2, mul_assoc, dM_inv, mul_one]

/-- The unit-level doubling identity for `v₃`. -/
theorem dU_conj_v3U : dU * v3U * dU⁻¹ = v3U * v3U := by
  apply Units.ext
  change dM * v3M * dInvM = v3M * v3M
  rw [rel_d_v3, mul_assoc, dM_inv, mul_one]

/-- Doubling on `v₁`. -/
theorem conjD_v1G : conjD v1G = v1G ^ 2 := by
  apply Subtype.ext
  simpa [conjD, v1G, pow_two] using dU_conj_v1U

/-- Doubling on `v₂`. -/
theorem conjD_v2G : conjD v2G = v2G ^ 2 := by
  apply Subtype.ext
  simpa [conjD, v2G, pow_two] using dU_conj_v2U

/-- Doubling on `v₃`. -/
theorem conjD_v3G : conjD v3G = v3G ^ 2 := by
  apply Subtype.ext
  simpa [conjD, v3G, pow_two] using dU_conj_v3U

/-- The doubling conjugation fixes `x`. -/
theorem conjD_xG : conjD xG = xG := by
  apply Subtype.ext
  change dU * xU * dU⁻¹ = xU
  apply Units.ext
  change dM * xM * dInvM = xM
  rw [rel_d_x, mul_assoc, dM_inv, mul_one]

/-- The doubling conjugation fixes `y`. -/
theorem conjD_yG : conjD yG = yG := by
  apply Subtype.ext
  change dU * yU * dU⁻¹ = yU
  apply Units.ext
  change dM * yM * dInvM = yM
  rw [rel_d_y, mul_assoc, dM_inv, mul_one]

/-- The doubling conjugation fixes `z`. -/
theorem conjD_zG : conjD zG = zG := by
  apply Subtype.ext
  change dU * zU * dU⁻¹ = zU
  apply Units.ext
  change dM * zM * dInvM = zM
  rw [rel_d_z, mul_assoc, dM_inv, mul_one]

/-- Doubling on each of the six exact affine generators. -/
theorem conjD_matrixBaseGenerator (i : BaseGenerator) :
    conjD (matrixBaseGenerator i) =
      FreeGroup.lift matrixBaseGenerator (compressedBaseWord i) := by
  fin_cases i
  · simpa [matrixBaseGenerator, compressedBaseWord, v1Index] using conjD_v1G
  · simpa [matrixBaseGenerator, compressedBaseWord, v1Index, v2Index] using
      conjD_v2G
  · simpa [matrixBaseGenerator, compressedBaseWord, v1Index, v2Index,
      v3Index] using conjD_v3G
  · simpa [matrixBaseGenerator, compressedBaseWord, v1Index, v2Index,
      v3Index, xIndex] using conjD_xG
  · simpa [matrixBaseGenerator, compressedBaseWord, v1Index, v2Index,
      v3Index, xIndex, yIndex] using conjD_yG
  · simpa [matrixBaseGenerator, compressedBaseWord, v1Index, v2Index,
      v3Index, xIndex, yIndex, zIndex] using conjD_zG

/-- The exact target data for every relation of the literal presentation. -/
noncomputable def realization : Realization WitnessGroup where
  baseGenerator := witnessBaseGenerator
  stable := tAmbient alpha conjD_injective
  lamp := cAmbient alpha conjD_injective
  base_relations := witnessBaseGenerator_kills
  stable_relations i := by
    simp only [witnessBaseGenerator]
    rw [compress]
    rw [conjD_matrixBaseGenerator]
    symm
    exact witness_eval_base (compressedBaseWord i)
  lamp_sq := cAmbient_sq alpha conjD_injective
  lamp_centralizes_base i := comm_c alpha conjD_injective _
  marked_central g := by
    simp only [witnessBaseGenerator, matrixBaseGenerator_v1]
    rw [marked_word_eq_sign alpha conjD_injective v1G_not_mem_range]
    exact signAmbient_central alpha conjD_injective g

theorem realization_marked_word :
    markedCompressionWord realization.stable
      (realization.baseGenerator v1Index) realization.lamp =
        signAmbient alpha conjD_injective := by
  simp only [realization, witnessBaseGenerator, matrixBaseGenerator_v1]
  exact marked_word_eq_sign alpha conjD_injective v1G_not_mem_range

/-- The homomorphism from the literal eight-generator presentation to its
explicit affine--Clifford witness. -/
noncomputable def witnessHom : MarkedGroup →* WitnessGroup :=
  realizationHom realization

/-- The literal marked word maps exactly to the nontrivial central Clifford
sign in the witness group. -/
@[simp] theorem witnessHom_mark :
    witnessHom mark = signAmbient alpha conjD_injective := by
  rw [witnessHom, realizationHom_mark, realization_marked_word]

@[simp] theorem witnessHom_base_generator (i : BaseGenerator) :
    witnessHom (baseMap (PresentedGroup.of i)) =
      iotaAmbient alpha conjD_injective (matrixBaseGenerator i) := by
  rw [witnessHom, realizationHom_base_generator]
  rfl

@[simp] theorem witnessHom_stable :
    witnessHom stable = tAmbient alpha conjD_injective := by
  simp [witnessHom, realization]

@[simp] theorem witnessHom_lamp :
    witnessHom lamp = cAmbient alpha conjD_injective := by
  simp [witnessHom, realization]

/-- Every element of the affine base copy belongs to the range of the
literal witness homomorphism. -/
theorem iotaAmbient_mem_witnessHom_range (γ : gammaBar) :
    iotaAmbient alpha conjD_injective γ ∈ witnessHom.range := by
  let K : Subgroup gammaBar :=
    witnessHom.range.comap (iotaAmbient alpha conjD_injective)
  have hgen (i : BaseGenerator) : matrixBaseGenerator i ∈ K := by
    exact ⟨baseMap (PresentedGroup.of i), witnessHom_base_generator i⟩
  have hgenerators :
      gammaBar.subtype ⁻¹' ({xU, yU, zU, v1U, v2U, v3U} : Set Matˣ) ⊆ K := by
    intro u hu
    rcases hu with h | h | h | h | h | h
    · rw [show u = xG from Subtype.ext h]
      simpa [matrixBaseGenerator, v1Index, v2Index, v3Index, xIndex]
        using hgen xIndex
    · rw [show u = yG from Subtype.ext h]
      simpa [matrixBaseGenerator, v1Index, v2Index, v3Index, xIndex, yIndex]
        using hgen yIndex
    · rw [show u = zG from Subtype.ext h]
      simpa [matrixBaseGenerator, v1Index, v2Index, v3Index, xIndex, yIndex,
        zIndex] using hgen zIndex
    · rw [show u = v1G from Subtype.ext h]
      simpa [matrixBaseGenerator] using hgen v1Index
    · rw [show u = v2G from Subtype.ext h]
      simpa [matrixBaseGenerator, v1Index, v2Index] using hgen v2Index
    · rw [Set.mem_singleton_iff] at h
      rw [show u = v3G from Subtype.ext h]
      simpa [matrixBaseGenerator, v1Index, v2Index, v3Index] using hgen v3Index
  have hclosure :
      Subgroup.closure
          (gammaBar.subtype ⁻¹'
            ({xU, yU, zU, v1U, v2U, v3U} : Set Matˣ)) ≤ K :=
    (Subgroup.closure_le _).mpr hgenerators
  have htop :
      Subgroup.closure
          (gammaBar.subtype ⁻¹'
            ({xU, yU, zU, v1U, v2U, v3U} : Set Matˣ)) = ⊤ := by
    exact Subgroup.closure_preimage_eq_top
      ({xU, yU, zU, v1U, v2U, v3U} : Set Matˣ)
  exact hclosure (htop.symm ▸ Subgroup.mem_top γ)

/-- The literal homomorphism onto the affine--Clifford witness is
surjective, as asserted in manuscript Proposition `prop:W`. -/
theorem witnessHom_surjective : Function.Surjective witnessHom := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  intro g _
  apply ambient_mem_subgroup_of_generators_mem alpha conjD_injective
    witnessHom.range
  · exact iotaAmbient_mem_witnessHom_range
  · exact ⟨stable, witnessHom_stable⟩
  · exact ⟨lamp, witnessHom_lamp⟩
  · exact ⟨mark, witnessHom_mark⟩

/-- The explicit affine--Clifford witness is finitely generated, as the
surjective image of the literal finite presentation. -/
theorem witnessGroup_finitelyGenerated : Group.FG WitnessGroup := by
  letI : Group.FG MarkedGroup :=
    Group.fg_of_surjective
      (PresentedGroup.mk_surjective
        (relators : Set (FreeGroup Generator)))
  exact Group.fg_of_surjective witnessHom_surjective

/-- **Exact separation of the literal mark.** -/
theorem literal_mark_ne_one : mark ≠ 1 := by
  apply mark_ne_one_of_realization realization
  rw [realization_marked_word]
  exact signAmbient_ne_one alpha conjD_injective

/-- The exact algebraic package for the literal manuscript group. -/
theorem literal_finitelyPresented_nontrivial_mark :
    Group.IsFinitelyPresented MarkedGroup ∧ mark ^ 2 = 1 ∧
      (∀ g : MarkedGroup, Commute mark g) ∧ mark ≠ 1 := by
  exact ⟨inferInstance, mark_sq, mark_central, literal_mark_ne_one⟩

end

end LiteralNonMFLinearWitness
end GroupApproximation
