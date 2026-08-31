import GroupApproximation.Analysis.STW22TypeIC0Sum
import GroupApproximation.Analysis.StateExtension
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Topological Schur lemma for irreducible C-star representations

This file proves the analytic Schur lemma needed for the type-I verification of
the antipodal homogeneous blocks.  The proof uses only continuous functional
calculus.  If a self-adjoint operator in the commutant is not scalar, two
continuous functions supported on opposite sides of a midpoint produce
nonzero commuting operators `x` and `y` with `y * x = 0`.  The closure of the
range of `x` is then a nonzero proper invariant subspace.
-/

namespace GroupApproximation
namespace STW22

noncomputable section

open scoped CStarAlgebra ComplexOrder
open StateExtension

universe u

variable {A H : Type u} [CStarAlgebra A] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

private def lowerBump (r : ℝ) : ℝ → ℝ := fun t ↦ max (r - t) 0

private def upperBump (r : ℝ) : ℝ → ℝ := fun t ↦ max (t - r) 0

private theorem continuous_lowerBump (r : ℝ) : Continuous (lowerBump r) := by
  unfold lowerBump
  fun_prop

private theorem continuous_upperBump (r : ℝ) : Continuous (upperBump r) := by
  unfold upperBump
  fun_prop

private theorem lowerBump_mul_upperBump (r t : ℝ) :
    lowerBump r t * upperBump r t = 0 := by
  unfold lowerBump upperBump
  by_cases h : t ≤ r
  · rw [max_eq_right (sub_nonpos.mpr h)]
    exact mul_zero _
  · have h' : r ≤ t := le_of_not_ge h
    rw [max_eq_right (sub_nonpos.mpr h')]
    exact zero_mul _

/-- A self-adjoint operator in the commutant of a topologically irreducible
C-star representation is scalar.  This is the bounded-operator Schur lemma,
proved using only continuous functional calculus and closed ranges. -/
theorem IsIrreducibleRep.selfAdjoint_commutant_eq_scalar
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} (hπ : IsIrreducibleRep π)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hcomm : ∀ a : A, Commute T (π a)) :
    ∃ r : ℝ, T = algebraMap ℝ (H →L[ℂ] H) r := by
  obtain ⟨v₀, hv₀⟩ := hπ.exists_ne_zero
  letI : Nontrivial H := ⟨⟨v₀, 0, hv₀⟩⟩
  letI : ContinuousFunctionalCalculus ℂ (H →L[ℂ] H) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus ℝ (H →L[ℂ] H) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  obtain ⟨α, hα⟩ :=
    ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) T hT
  by_cases hs : spectrum ℝ T ⊆ {α}
  · exact ⟨α, CFC.eq_algebraMap_of_spectrum_subset_singleton T α hs hT⟩
  · obtain ⟨β, hβ, hβα⟩ := Set.not_subset.mp hs
    have hne : β ≠ α := by simpa using hβα
    obtain ⟨a, b, ha, hb, hlt⟩ :
        ∃ a b : ℝ, a ∈ spectrum ℝ T ∧ b ∈ spectrum ℝ T ∧ a < b := by
      rcases lt_or_gt_of_ne hne with hβα | hαβ
      · exact ⟨β, α, hβ, hα, hβα⟩
      · exact ⟨α, β, hα, hβ, hαβ⟩
    let r : ℝ := (a + b) / 2
    let f : C(spectrum ℝ T, ℝ) :=
      ⟨fun t ↦ lowerBump r t,
        (continuous_lowerBump r).comp continuous_subtype_val⟩
    let g : C(spectrum ℝ T, ℝ) :=
      ⟨fun t ↦ upperBump r t,
        (continuous_upperBump r).comp continuous_subtype_val⟩
    let X : H →L[ℂ] H := cfcHom hT f
    let Y : H →L[ℂ] H := cfcHom hT g
    have hf_ne : f ≠ 0 := by
      intro hf
      have hv := congrArg (fun q : C(spectrum ℝ T, ℝ) ↦ q ⟨a, ha⟩) hf
      change lowerBump r a = 0 at hv
      have hpos : 0 < r - a := by dsimp [r]; linarith
      rw [lowerBump, max_eq_left (le_of_lt hpos)] at hv
      exact (ne_of_gt hpos) hv
    have hg_ne : g ≠ 0 := by
      intro hg
      have hv := congrArg (fun q : C(spectrum ℝ T, ℝ) ↦ q ⟨b, hb⟩) hg
      change upperBump r b = 0 at hv
      have hpos : 0 < b - r := by dsimp [r]; linarith
      rw [upperBump, max_eq_left (le_of_lt hpos)] at hv
      exact (ne_of_gt hpos) hv
    have hX_ne : X ≠ 0 := by
      intro hX
      apply hf_ne
      exact cfcHom_injective hT (by simpa [X] using hX)
    have hY_ne : Y ≠ 0 := by
      intro hY
      apply hg_ne
      exact cfcHom_injective hT (by simpa [Y] using hY)
    have hYX : Y * X = 0 := by
      change cfcHom hT g * cfcHom hT f = 0
      rw [← map_mul]
      rw [show g * f = 0 by
        ext t
        change upperBump r t * lowerBump r t = 0
        rw [mul_comm]
        exact lowerBump_mul_upperBump r t]
      exact map_zero _
    have hXcomm : ∀ a : A, Commute X (π a) := by
      intro a
      exact hT.commute_cfcHom hT (hcomm a) f
    let M : Submodule ℂ H := (LinearMap.range (X : H →ₗ[ℂ] H)).topologicalClosure
    have hMclosed : IsClosed (M : Set H) := Submodule.isClosed_topologicalClosure _
    have hMinv : ∀ a : A, ∀ x ∈ M, π a x ∈ M := by
      intro a x hx
      apply mapsTo_topologicalClosure (π a) (P := LinearMap.range (X : H →ₗ[ℂ] H))
        (fun _ hx' ↦ ?_) x hx
      obtain ⟨v, rfl⟩ := hx'
      refine ⟨π a v, ?_⟩
      have hv := congrArg (fun S : H →L[ℂ] H ↦ S v) (hXcomm a).eq
      change X (π a v) = π a (X v) at hv
      exact hv
    have hMne : M ≠ ⊥ := by
      intro hbot
      apply hX_ne
      ext v
      have hmem : X v ∈ M := Submodule.le_topologicalClosure _
        (LinearMap.mem_range_self (X : H →ₗ[ℂ] H) v)
      rw [hbot] at hmem
      exact (Submodule.mem_bot ℂ).mp hmem
    have hMle : M ≤ LinearMap.ker (Y : H →ₗ[ℂ] H) := by
      apply Submodule.topologicalClosure_minimal
      · rintro _ ⟨v, rfl⟩
        rw [LinearMap.mem_ker]
        have hv := congrArg (fun S : H →L[ℂ] H ↦ S v) hYX
        change Y (X v) = 0 at hv
        exact hv
      · exact Y.isClosed_ker
    have hMtop : M ≠ ⊤ := by
      intro htop
      apply hY_ne
      ext v
      have hv : v ∈ M := by rw [htop]; exact Submodule.mem_top
      exact (LinearMap.mem_ker.mp (hMle hv))
    rcases hπ.2 M ⟨hMclosed, hMinv⟩ with hbot | htop
    · exact (hMne hbot).elim
    · exact (hMtop htop).elim

/-- Full topological Schur lemma: an operator whose real and imaginary parts
belong to the commutant of an irreducible C-star representation is a complex
scalar.  The separate hypothesis for `star T` is exactly what is automatic for
the image of a central element of the represented star algebra. -/
theorem IsIrreducibleRep.commutant_eq_scalar
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} (hπ : IsIrreducibleRep π)
    (T : H →L[ℂ] H)
    (hcomm : ∀ a : A, Commute T (π a))
    (hstarcomm : ∀ a : A, Commute (star T) (π a)) :
    ∃ c : ℂ, T = algebraMap ℂ (H →L[ℂ] H) c := by
  let R : H →L[ℂ] H := ((rePart T : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)
  let S : H →L[ℂ] H := ((imPart T : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)
  have hRcomm : ∀ a : A, Commute R (π a) := by
    intro a
    dsimp [R]
    exact ((hcomm a).add_left (hstarcomm a)).smul_left _
  have hScomm : ∀ a : A, Commute S (π a) := by
    intro a
    dsimp [S]
    exact (((hcomm a).sub_left (hstarcomm a)).smul_left _).smul_left _
  obtain ⟨r, hr⟩ := hπ.selfAdjoint_commutant_eq_scalar R (rePart T).2 hRcomm
  obtain ⟨s, hs⟩ := hπ.selfAdjoint_commutant_eq_scalar S (imPart T).2 hScomm
  refine ⟨(r : ℂ) + Complex.I * (s : ℂ), ?_⟩
  calc
    T = R + Complex.I • S := (rePart_add_I_smul_imPart T).symm
    _ = algebraMap ℝ (H →L[ℂ] H) r +
        Complex.I • algebraMap ℝ (H →L[ℂ] H) s := by rw [hr, hs]
    _ = algebraMap ℂ (H →L[ℂ] H) ((r : ℂ) + Complex.I * (s : ℂ)) := by
      ext v
      change (r : ℂ) • v + Complex.I • ((s : ℂ) • v) =
        ((r : ℂ) + Complex.I * (s : ℂ)) • v
      rw [smul_smul, add_smul]

/-- The image of a central element in an irreducible C-star representation is
a scalar.  No algebraic or Borel-functional-calculus Schur lemma is assumed. -/
theorem IsIrreducibleRep.map_center_eq_scalar
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} (hπ : IsIrreducibleRep π)
    (z : A) (hz : ∀ a : A, z * a = a * z) :
    ∃ c : ℂ, π z = algebraMap ℂ (H →L[ℂ] H) c := by
  apply hπ.commutant_eq_scalar (π z)
  · intro a
    rw [commute_iff_eq, ← map_mul, ← map_mul, hz]
  · intro a
    rw [← map_star]
    rw [commute_iff_eq, ← map_mul, ← map_mul]
    have h := congrArg star (hz (star a))
    exact congrArg π (by simpa only [star_mul, star_star] using h.symm)

end

end STW22
end GroupApproximation
