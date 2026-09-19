import GroupApproximation.Sofic.FiniteNormalCompressionObstruction
import GroupApproximation.Sofic.IntrinsicCompressionDefect
import GroupApproximation.Sofic.KazhdanAsymptoticCommutant

/-!
# The intrinsic compression defect lies in the MF radical on finite normals

This file joins the all-compressors asymptotic-commutant theorem to the
Reynolds-corner argument.  It contains no distinguished compressor, lamp, or
marked word.
-/

namespace GroupApproximation
namespace KazhdanAsymptoticCommutant

open Filter KazhdanCornerMatrices KazhdanCompressorCorner
open scoped commutatorElement Matrix.Norms.L2Operator

variable {Gamma E : Type} [Group Gamma] [Group E]

/-- Hilbert--Schmidt coincidence of two coordinate microstates is equality in
the associated tracial ultraproduct. -/
theorem eq_in_hyperlinearHom_of_hsSqVanishing
    (B : OpAlmostRepresentation E) {U : Ultrafilter Nat}
    (hcof : (U : Filter Nat) ≤ Filter.cofinite) (g h : E)
    (hgh : HSSqVanishing B (fun n ↦
      (B.map n g : Matrix (B.model n) (B.model n) Complex) - B.map n h)) :
    (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof g =
      (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof h := by
  let S := KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B
  let rhoHS : E →* UniversalHyperlinear U S.model S.modelNonempty :=
    S.toUltraproductHom hcof
  have hnull :
      (fun n ↦ S.map n g)⁻¹ * (fun n ↦ S.map n h) ∈
        nullUnitarySubgroup U S.model S.modelNonempty := by
    intro epsilon hepsilon
    obtain ⟨N, hN⟩ := hgh (epsilon / 2) (by linarith)
    refine eventually_of_atTop hcof N (fun n hn ↦ ?_)
    show hsLengthSq (S.model n)
      (((S.map n g)⁻¹ * S.map n h : Matrix.unitaryGroup (S.model n) Complex)) < epsilon
    rw [coe_inv_mul,
      hsLengthSq_conjTranspose_mul (S.model n) (S.map n g).2
        (S.modelNonempty n),
      KazhdanCompressorCorner.hsDistSq_comm]
    exact lt_of_le_of_lt (hN n hn) (by linarith)
  have heq :
      QuotientGroup.mk (fun n ↦ S.map n g) =
        QuotientGroup.mk (fun n ↦ S.map n h) :=
    QuotientGroup.eq.mpr hnull
  change rhoHS g = rhoHS h
  exact heq

/-- An exact centralizer element gives a bounded sequence in the asymptotic
commutant. -/
theorem map_mem_asymptoticCommutantOf
    (B : OpAlmostRepresentation E) (iota : Gamma →* E) (z : E)
    (hz : ∀ delta ∈ iota.range, Commute z delta) :
    IsAsymptoticCommutantOf B iota (fun n ↦
      (B.map n z : Matrix (B.model n) (B.model n) Complex)) := by
  intro gamma
  have hconj : iota gamma * z * (iota gamma)⁻¹ = z := by
    have hcomm := (hz (iota gamma) ⟨gamma, rfl⟩).eq
    calc
      iota gamma * z * (iota gamma)⁻¹ =
          (z * iota gamma) * (iota gamma)⁻¹ := by rw [hcomm]
      _ = z := by group
  have hdef := (conj_matrix_defect_vanishing B (iota gamma) z).neg
  apply HSSqVanishing.of_opNormVanishing
  exact hdef.congr fun n ↦ by
    rw [hconj]
    abel

/-- Every intrinsic compression--centralizer generator is killed in the
tracial ultraproduct associated to every operator-norm almost representation. -/
theorem compressionCentralizerDefect_generator_eq_one_in_hyperlinearHom
    (B : OpAlmostRepresentation E) (iota : Gamma →* E)
    (hkazhdan : HasKazhdanPropertyT.{0, 0} Gamma)
    {U : Ultrafilter Nat} (hcof : (U : Filter Nat) ≤ Filter.cofinite)
    {g z ell : E} (hg : g ∈ compressionGroup iota.range)
    (hz : ∀ delta ∈ iota.range, Commute z delta)
    (hell : ell ∈ iota.range) :
    (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof ⁅g * z * g⁻¹, ell⁆ = 1 := by
  let x : ∀ n, Matrix (B.model n) (B.model n) Complex := fun n ↦ B.map n z
  have hbound : IsUniformlyBounded B x := ⟨1, zero_le_one, fun n ↦ by
    letI : Nonempty (B.model n) :=
      Fintype.card_pos_iff.mp (B.modelNonempty n)
    exact (CStarRing.norm_of_mem_unitary (B.map n z).2).le⟩
  have hx : IsAsymptoticCommutantOf B iota x :=
    map_mem_asymptoticCommutantOf B iota z hz
  have htransport := (compressionGroup_transport_both B iota hkazhdan hg x hbound hx).1
  let y : E := g * z * g⁻¹
  have hy : IsAsymptoticCommutantOf B iota (fun n ↦
      (B.map n y : Matrix (B.model n) (B.model n) Complex)) := by
    apply IsAsymptoticCommutant.congr_hs htransport
    apply HSSqVanishing.of_opNormVanishing
    simpa [adjointSequence, x, y] using conj_matrix_defect_vanishing B g z
  obtain ⟨gamma, rfl⟩ := hell
  have hcommuteHS := hy gamma
  have htrack := HSSqVanishing.of_opNormVanishing
    (conj_matrix_defect_vanishing B (iota gamma) y)
  have heqHS : HSSqVanishing B (fun n ↦
      (B.map n y : Matrix (B.model n) (B.model n) Complex) -
        B.map n (iota gamma * y * (iota gamma)⁻¹)) := by
    exact (hcommuteHS.add htrack).congr fun n ↦ by abel
  let S := KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B
  let rhoHS : E →* UniversalHyperlinear U S.model S.modelNonempty :=
    S.toUltraproductHom hcof
  have heq : rhoHS y = rhoHS (iota gamma * y * (iota gamma)⁻¹) :=
    eq_in_hyperlinearHom_of_hsSqVanishing B hcof y
      (iota gamma * y * (iota gamma)⁻¹) heqHS
  have hconj :
      rhoHS (iota gamma) * rhoHS y * (rhoHS (iota gamma))⁻¹ = rhoHS y := by
    simpa only [map_mul, map_inv] using heq.symm
  have hcomm : Commute (rhoHS y) (rhoHS (iota gamma)) := by
    apply Commute.symm
    show rhoHS (iota gamma) * rhoHS y = rhoHS y * rhoHS (iota gamma)
    calc
      rhoHS (iota gamma) * rhoHS y =
          (rhoHS (iota gamma) * rhoHS y * (rhoHS (iota gamma))⁻¹) *
            rhoHS (iota gamma) := by group
      _ = rhoHS y * rhoHS (iota gamma) := by rw [hconj]
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr hcomm

/-- The entire intrinsic defect is killed in every tracial ultraproduct
arising from an operator-norm almost representation. -/
theorem compressionCentralizerDefect_eq_one_in_hyperlinearHom
    (B : OpAlmostRepresentation E) (iota : Gamma →* E)
    (hkazhdan : HasKazhdanPropertyT.{0, 0} Gamma)
    {U : Ultrafilter Nat} (hcof : (U : Filter Nat) ≤ Filter.cofinite) :
    compressionCentralizerDefect iota.range ≤
      ((KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof).ker := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨g, hg, z, hz, ell, hell, rfl⟩
  exact MonoidHom.mem_ker.mpr
    (compressionCentralizerDefect_generator_eq_one_in_hyperlinearHom
      B iota hkazhdan hcof hg hz hell)

/-- **Intrinsic compression-radical theorem.**  Every finite normal subgroup
inside the intrinsic compression--centralizer defect of a Kazhdan image lies
in the norm-MF residual. -/
theorem finiteNormal_le_normMFResidual_of_le_compressionCentralizerDefect
    [Countable E] (iota : Gamma →* E)
    (hkazhdan : HasKazhdanPropertyT.{0, 0} Gamma)
    (F : Subgroup E) [Finite F] [F.Normal]
    (hF : F ≤ compressionCentralizerDefect iota.range) :
    F ≤ normMFResidual E := by
  refine KazhdanCompressionCore.finiteNormal_le_normMFResidual_of_hyperlinear_killed
    (compressionCentralizerDefect iota.range) ?_ F hF
  intro B U hcof x hx
  exact MonoidHom.mem_ker.mp
    (compressionCentralizerDefect_eq_one_in_hyperlinearHom
      B iota hkazhdan hcof hx)

end KazhdanAsymptoticCommutant
end GroupApproximation
