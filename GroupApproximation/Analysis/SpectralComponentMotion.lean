import GroupApproximation.Analysis.ClopenSpectralProjection

/-!
# Spectral-component motion in a noncommutative C-star algebra

Commuting normal elements generate a commutative C-star algebra.  Consequently,
if their clopen spectral projections agree, their distance is bounded by the
diameters of the connected components of the spectrum.  This is the bridge
from projection collapse in a matrix corona to the quantitative spectral
compression theorem.
-/

namespace GroupApproximation
namespace SpectralComponentMotion

open ClopenSpectralProjection SpectralComponentDiameter WeakDual
open scoped IsMulCommutative

universe u

variable {A : Type u} [CStarAlgebra A]

noncomputable local instance :
    ContinuousFunctionalCalculus ℂ A IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

/-- Two commuting normal elements whose clopen spectral projections agree can
move only within connected components of their common spectrum. -/
theorem norm_sub_le_of_clopen_projections_eq
    (a b : A) (ha : IsStarNormal a) (hb : IsStarNormal b)
    (hab : Commute a b) (hspectrum : spectrum ℂ b = spectrum ℂ a)
    (hprojection : ∀ (U : Set (spectrum ℂ a)) (hU : IsClopen U),
      projection a U hU = cfc (spectralIndicator a U hU) b)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hdiameter : ∀ z : spectrum ℂ a,
      Metric.diam (connectedComponent z) ≤ δ) :
    ‖a - b‖ ≤ δ := by
  classical
  let S : StarSubalgebra ℂ A :=
    (StarAlgebra.adjoin ℂ ({a, b} : Set A)).topologicalClosure
  have hS : IsClosed (S : Set A) :=
    (StarAlgebra.adjoin ℂ ({a, b} : Set A)).isClosed_topologicalClosure
  have hcommLeft := ha.commute_star_left hab
  have hcommRight := hb.commute_star_right hab
  have hmul : IsMulCommutative (StarAlgebra.adjoin ℂ ({a, b} : Set A)) :=
    StarAlgebra.isMulCommutative_adjoin ℂ (by grind)
      (by grind [commute_star_comm])
  letI : IsMulCommutative (StarAlgebra.adjoin ℂ ({a, b} : Set A)) := hmul
  let _ : CommRing S :=
    (StarAlgebra.adjoin ℂ ({a, b} : Set A)).commRingTopologicalClosure mul_comm
  let _ : CommCStarAlgebra S := {}
  letI : ContinuousFunctionalCalculus ℂ S IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  have haS : a ∈ S := by
    apply StarSubalgebra.le_topologicalClosure
    exact StarAlgebra.subset_adjoin ℂ ({a, b} : Set A) (by simp)
  have hbS : b ∈ S := by
    apply StarSubalgebra.le_topologicalClosure
    exact StarAlgebra.subset_adjoin ℂ ({a, b} : Set A) (by simp)
  let aa : S := ⟨a, haS⟩
  let bb : S := ⟨b, hbS⟩
  have haa : IsStarNormal aa := ⟨mul_comm _ _⟩
  have hbb : IsStarNormal bb := ⟨mul_comm _ _⟩
  have hspecA : spectrum ℂ aa = spectrum ℂ a :=
    StarSubalgebra.spectrum_eq S
  have hspecB : spectrum ℂ bb = spectrum ℂ b :=
    StarSubalgebra.spectrum_eq S
  have hclopen : ∀ χ : characterSpace ℂ S,
      ∀ U : Set (spectrum ℂ a), IsClopen U →
        ((⟨χ aa, hspecA ▸
              (CharacterSpace.mem_spectrum_iff_exists).2 ⟨χ, rfl⟩⟩ :
            spectrum ℂ a) ∈ U ↔
          (⟨χ bb, hspectrum ▸ hspecB ▸
              (CharacterSpace.mem_spectrum_iff_exists).2 ⟨χ, rfl⟩⟩ :
            spectrum ℂ a) ∈ U) := by
    intro χ U hU
    let f := spectralIndicator a U hU
    have hfA : ContinuousOn f (spectrum ℂ aa) := by
      rw [hspecA]
      exact spectralIndicator_continuousOn hU
    have hfB : ContinuousOn f (spectrum ℂ bb) := by
      rw [hspecB, hspectrum]
      exact spectralIndicator_continuousOn hU
    have hpS : cfc f aa = cfc f bb := by
      apply Subtype.ext
      change S.subtype (cfc f aa) = S.subtype (cfc f bb)
      rw [StarAlgHomClass.map_cfc S.subtype f aa hfA]
      rw [StarAlgHomClass.map_cfc S.subtype f bb hfB]
      simpa [f, projection, aa, bb] using hprojection U hU
    have hvalues := congrArg χ hpS
    rw [StarAlgHomClass.map_cfc χ f aa hfA,
      StarAlgHomClass.map_cfc χ f bb hfB,
      cfc_complex_eq_apply, cfc_complex_eq_apply] at hvalues
    let za : spectrum ℂ a := ⟨χ aa, hspecA ▸
      (CharacterSpace.mem_spectrum_iff_exists).2 ⟨χ, rfl⟩⟩
    let zb : spectrum ℂ a := ⟨χ bb, hspectrum ▸ hspecB ▸
      (CharacterSpace.mem_spectrum_iff_exists).2 ⟨χ, rfl⟩⟩
    change za ∈ U ↔ zb ∈ U
    have hvalues' : spectralIndicator a U hU za =
        spectralIndicator a U hU zb := by
      simpa [f, za, zb] using hvalues
    rw [spectralIndicator_apply_of_mem hU za,
      spectralIndicator_apply_of_mem hU zb] at hvalues'
    by_cases hza : za ∈ U <;> by_cases hzb : zb ∈ U <;>
      simp_all [Set.indicator_of_mem, Set.indicator_of_notMem]
  change ‖aa - bb‖ ≤ δ
  rw [← (gelfandTransform_isometry S).norm_map_of_map_zero
      (map_zero (gelfandTransform ℂ S)) (aa - bb)]
  apply (ContinuousMap.norm_le ((gelfandTransform ℂ S) (aa - bb)) hδ).2
  intro χ
  let za : spectrum ℂ a := ⟨χ aa, hspecA ▸
    (CharacterSpace.mem_spectrum_iff_exists).2 ⟨χ, rfl⟩⟩
  let zb : spectrum ℂ a := ⟨χ bb, hspectrum ▸ hspecB ▸
    (CharacterSpace.mem_spectrum_iff_exists).2 ⟨χ, rfl⟩⟩
  have hcomponent : zb ∈ connectedComponent za :=
    mem_connectedComponent_of_same_clopens (fun U hU ↦ hclopen χ U hU)
  have hdist : dist za zb ≤ Metric.diam (connectedComponent za) :=
    Metric.dist_le_diam_of_mem
      isClosed_connectedComponent.isCompact.isBounded
      mem_connectedComponent hcomponent
  have hpoint : dist za zb ≤ δ := hdist.trans (hdiameter za)
  simpa [za, zb, Subtype.dist_eq, Complex.dist_eq, map_sub, aa, bb] using hpoint

end SpectralComponentMotion
end GroupApproximation

