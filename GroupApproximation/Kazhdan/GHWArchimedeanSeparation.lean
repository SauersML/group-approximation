import GroupApproximation.Kazhdan.GHWArchimedeanMinkowski
import GroupApproximation.Kazhdan.GHWArchimedeanWedge
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import GroupApproximation.Meta.AxiomGuard

/-!
# The walls separating two points of hyperbolic space

Guentner--Higson--Weinberger, *The Novikov conjecture for linear groups* (Publ. Math. IHÉS 101
(2005)), §5, Lemma 8, at an archimedean place.  In the notation of
`Kazhdan/GHWArchimedeanMinkowski`, `g ∈ GL₂(ℂ)` moves the base point `origin = diag(1, 1)` to
`conjAct g origin`, whose Hermitian matrix is `|det g|⁻¹ g g*`.  The half-space of a point `x`
is `{v : 0 < B(x, v)}` (`posSide x`, which is `Walls.halfSpace x` by definition).

* `exists_unitary_diagPoint`: **spectral reduction**.  `conjAct g origin = conjAct U (diag(a, b))`
  with `U` unitary, `a, b > 0` the eigenvalues of `g g*/|det g|`, `ab = 1`, and
  `|det g| (a + b) = Σ |g_ij|²`.
* `shellMeasure_symmDiff_conjAct_unitary`: a unitary fixes the base point and preserves the shell
  measure, so it does not change the measure of the separating walls.
* `shellMeasure_symmDiff_diagPoint_lt_top`, `volume_diagonal_sep_ge`: at `diag(a, b)` the
  separating walls lie in the bounded set of `Kazhdan/GHWArchimedeanWedge` and contain its wedge,
  so their shell measure is finite and at least `2|log a|·φ(1)`.
* `separation_bound`, `separation_diff_lt_top`: both statements for every `g`, which is what the
  wall action of `Kazhdan/GHWArchimedeanWalls` needs (`SeparationFinite`) and what the bound
  `Kazhdan/GHWArchimedeanBound` consumes, with `κ = 2φ(1) > 0`.

## Manuscript status

Infrastructure for the Toeplitz--Jacobson remark (tex line 1146, "every countable subgroup of
`GL_2` over a field has the Haagerup property [GHW, Theorem 4]"); certifies no printed sentence
on its own.
-/

namespace GroupApproximation
namespace GHW
namespace Wedge

open MeasureTheory Set Matrix Minkowski Unitary

noncomputable section

theorem shell_eq_wedgeShell : shell = wedgeShell := rfl

/-- The half-space `{v : 0 < B(x, v)}` of a point `x`. -/
def posSide (x : Fin 4 → ℝ) : Set (Fin 4 → ℝ) := {v | 0 < lorentzB x v}

theorem measurableSet_posSide (x : Fin 4 → ℝ) : MeasurableSet (posSide x) := by
  have e : posSide x =
      {v : Fin 4 → ℝ | 0 < (x 0 * v 1 + x 1 * v 0) / 2 - x 2 * v 2 - x 3 * v 3} := by
    ext v
    simp only [posSide, Set.mem_setOf_eq, lorentzB_apply]
  rw [e]
  exact (isOpen_lt continuous_const (by fun_prop)).measurableSet

theorem posSide_diagPoint (a b : ℝ) :
    posSide (diagPoint a b) = {v | 0 < (b * v 0 + a * v 1) / 2} := by
  ext v
  simp only [posSide, Set.mem_setOf_eq, lorentzB_diagPoint]

theorem posSide_origin : posSide origin = {v | 0 < (v 0 + v 1) / 2} := by
  rw [show origin = diagPoint 1 1 from rfl, posSide_diagPoint]
  ext v
  simp only [Set.mem_setOf_eq, one_mul]

/-! ## At a diagonal point -/

/-- The walls separating `diag(1, 1)` from `diag(a, b)` lie in the bounded set of shell vectors
with `(v₀ + v₁)(b v₀ + a v₁) ≤ 0`. -/
theorem symmDiff_inter_shell_subset_sep (a b : ℝ) :
    symmDiff (posSide origin) (posSide (diagPoint a b)) ∩ shell ⊆
      {v : Fin 4 → ℝ | v ∈ wedgeShell ∧ (v 0 + v 1) * (b * v 0 + a * v 1) ≤ 0} := by
  rintro v ⟨hv, hs⟩
  rw [Set.mem_symmDiff, posSide_origin, posSide_diagPoint] at hv
  refine ⟨hs, ?_⟩
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' : 0 < (v 0 + v 1) / 2 := h1
    have h2' : ¬ 0 < (b * v 0 + a * v 1) / 2 := h2
    push Not at h2'
    nlinarith
  · have h1' : 0 < (b * v 0 + a * v 1) / 2 := h1
    have h2' : ¬ 0 < (v 0 + v 1) / 2 := h2
    push Not at h2'
    nlinarith

/-- The shell vectors with `(v₀ + v₁)(b v₀ + a v₁) < 0` separate `diag(1, 1)` from
`diag(a, b)`. -/
theorem sep_subset_symmDiff (a b : ℝ) :
    {v : Fin 4 → ℝ | v ∈ wedgeShell ∧ (v 0 + v 1) * (b * v 0 + a * v 1) < 0} ⊆
      symmDiff (posSide origin) (posSide (diagPoint a b)) ∩ shell := by
  rintro v ⟨hs, hpq⟩
  refine ⟨?_, hs⟩
  rw [Set.mem_symmDiff, posSide_origin, posSide_diagPoint]
  rcases lt_or_ge 0 (v 0 + v 1) with hp | hp
  · have hq : b * v 0 + a * v 1 < 0 := by nlinarith
    refine Or.inl ⟨show 0 < (v 0 + v 1) / 2 by linarith, fun h ↦ ?_⟩
    have h' : 0 < (b * v 0 + a * v 1) / 2 := h
    linarith
  · have hq : 0 < b * v 0 + a * v 1 := by nlinarith
    refine Or.inr ⟨show 0 < (b * v 0 + a * v 1) / 2 by linarith, fun h ↦ ?_⟩
    have h' : 0 < (v 0 + v 1) / 2 := h
    linarith

theorem measurableSet_symmDiff_posSide (x y : Fin 4 → ℝ) :
    MeasurableSet (symmDiff (posSide x) (posSide y)) :=
  (measurableSet_posSide x).symmDiff (measurableSet_posSide y)

/-- **At a diagonal point the separating walls have finite shell measure.** -/
theorem shellMeasure_symmDiff_diagPoint_lt_top {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    shellMeasure (symmDiff (posSide origin) (posSide (diagPoint a b))) < ⊤ := by
  rw [shellMeasure, Measure.restrict_apply (measurableSet_symmDiff_posSide _ _)]
  exact (measure_mono (symmDiff_inter_shell_subset_sep a b)).trans_lt (volume_sep_lt_top ha hb)

/-- **At `diag(a, a⁻¹)` the separating walls have shell measure at least `2|log a|·φ(1)`.** -/
theorem volume_diagonal_sep_ge {a b : ℝ} (ha : 0 < a) (hab : a * b = 1) :
    2 * |Real.log a| * wedgePhi 1 ≤
      (shellMeasure (symmDiff (posSide origin) (posSide (diagPoint a b)))).toReal := by
  have hb0 : 0 < b := by nlinarith
  have hb' : Real.exp (-Real.log a) = b := by
    rw [Real.exp_neg, Real.exp_log ha]
    exact (eq_inv_of_mul_eq_one_right hab).symm
  have h := volume_sep_ge (Real.log a)
  rw [hb', Real.exp_log ha] at h
  refine h.trans (ENNReal.toReal_mono (shellMeasure_symmDiff_diagPoint_lt_top ha hb0).ne ?_)
  rw [shellMeasure, Measure.restrict_apply (measurableSet_symmDiff_posSide _ _)]
  exact measure_mono (sep_subset_symmDiff a b)

/-! ## Unitary transport -/

theorem conjAct_preimage_posSide (g : GL (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    conjAct g ⁻¹' posSide (conjAct g x) = posSide x := by
  ext v
  simp only [Set.mem_preimage, posSide, Set.mem_setOf_eq, lorentzB_conjAct]

/-- **A unitary does not change the measure of the separating walls.** -/
theorem shellMeasure_symmDiff_conjAct_unitary {U : GL (Fin 2) ℂ}
    (hU : (U : Matrix (Fin 2) (Fin 2) ℂ) ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ))
    (w : Fin 4 → ℝ) :
    shellMeasure (symmDiff (posSide origin) (posSide (conjAct U w))) =
      shellMeasure (symmDiff (posSide origin) (posSide w)) := by
  have ho : conjAct U ⁻¹' posSide origin = posSide origin := by
    have h := conjAct_preimage_posSide U origin
    rwa [conjAct_origin_of_mem_unitary hU] at h
  have hpre : conjAct U ⁻¹' symmDiff (posSide origin) (posSide (conjAct U w)) =
      symmDiff (posSide origin) (posSide w) := by
    rw [Set.preimage_symmDiff, conjAct_preimage_posSide, ho]
  rw [← hpre]
  exact ((measurePreserving_conjAct_shell U).measure_preimage
    (measurableSet_symmDiff_posSide _ _).nullMeasurableSet).symm

/-! ## Spectral reduction -/

theorem norm_det_of_mem_unitary {U : GL (Fin 2) ℂ}
    (hU : (U : Matrix (Fin 2) (Fin 2) ℂ) ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ)) :
    ‖((U : Matrix (Fin 2) (Fin 2) ℂ)).det‖ = 1 := by
  have hgg : (U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.mul_star_self_of_mem hU
  have h := congrArg Matrix.det hgg
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, Complex.star_def,
    Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  have h2 : ‖((U : Matrix (Fin 2) (Fin 2) ℂ)).det‖ ^ 2 = 1 := by exact_mod_cast h
  have h3 := norm_nonneg ((U : Matrix (Fin 2) (Fin 2) ℂ)).det
  have hm : ‖((U : Matrix (Fin 2) (Fin 2) ℂ)).det‖ * ‖((U : Matrix (Fin 2) (Fin 2) ℂ)).det‖ = 1 := by
    rw [← sq]; exact h2
  rcases mul_self_eq_one_iff.mp hm with h1 | h1
  · exact h1
  · exact absurd h1 (by linarith [h3])

theorem herm_diagPoint (a b : ℝ) :
    herm (diagPoint a b) = Matrix.diagonal ![(a : ℂ), (b : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [herm, diagPoint]

theorem re_mul_conjTranspose_apply_self (M : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    ((M * Mᴴ) i i).re = ∑ j : Fin 2, ‖M i j‖ ^ 2 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, Complex.add_re]
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_re]

theorem conjAct_origin_zero (g : GL (Fin 2) ℂ) :
    conjAct g origin 0 = ‖((g : Matrix (Fin 2) (Fin 2) ℂ)).det‖⁻¹ *
      ∑ j : Fin 2, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 j‖ ^ 2 := by
  rw [conjAct_apply, herm_origin, Matrix.mul_one, Pi.smul_apply, smul_eq_mul,
    ← re_mul_conjTranspose_apply_self]
  rfl

theorem conjAct_origin_one (g : GL (Fin 2) ℂ) :
    conjAct g origin 1 = ‖((g : Matrix (Fin 2) (Fin 2) ℂ)).det‖⁻¹ *
      ∑ j : Fin 2, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 j‖ ^ 2 := by
  rw [conjAct_apply, herm_origin, Matrix.mul_one, Pi.smul_apply, smul_eq_mul,
    ← re_mul_conjTranspose_apply_self]
  rfl

/-- **Spectral reduction.**  `g` moves the base point to a unitary conjugate of `diag(a, b)`, with
`a, b > 0` the eigenvalues of `g g*/|det g|`, `ab = 1`, and `|det g|(a + b) = Σ |g_ij|²`. -/
theorem exists_unitary_diagPoint (g : GL (Fin 2) ℂ) :
    ∃ (U : GL (Fin 2) ℂ) (a b : ℝ),
      (U : Matrix (Fin 2) (Fin 2) ℂ) ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) ∧ 0 < a ∧ 0 < b ∧
        a * b = 1 ∧
        ‖((g : Matrix (Fin 2) (Fin 2) ℂ)).det‖ * (a + b) =
          ∑ i : Fin 2, ∑ j : Fin 2, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ^ 2 ∧
        conjAct g origin = conjAct U (diagPoint a b) := by
  classical
  set X := conjAct g origin with hXdef
  have hH : (herm X).IsHermitian := isHermitian_herm X
  let u := hH.eigenvectorUnitary
  let U : GL (Fin 2) ℂ := Unitary.toUnits u
  have hUcoe : (U : Matrix (Fin 2) (Fin 2) ℂ) = (u : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  have hUmem : (U : Matrix (Fin 2) (Fin 2) ℂ) ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hUcoe]
    exact u.2
  set a := hH.eigenvalues 0
  set b := hH.eigenvalues 1
  have hd : Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) =
      Matrix.diagonal ![(a : ℂ), (b : ℂ)] := by
    congr 1
    ext i
    fin_cases i <;> rfl
  have hspec : herm X =
      (u : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.diagonal ![(a : ℂ), (b : ℂ)] *
        (u : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
    have h := hH.spectral_theorem
    rw [conjStarAlgAut_apply, hd, Matrix.star_eq_conjTranspose] at h
    exact h
  have hdet : RCLike.re (herm X).det = 1 := by
    rw [RCLike.re_to_complex, lorentzQ_eq_re_det_herm, hXdef, lorentzQ_conjAct]
    simp [lorentzQ, origin]
  have hab : a * b = 1 := by
    have h := congrArg RCLike.re hH.det_eq_prod_eigenvalues
    rw [Fin.prod_univ_two, ← RCLike.ofReal_mul, RCLike.ofReal_re, hdet] at h
    exact h.symm
  have htrace : RCLike.re (herm X).trace = X 0 + X 1 := by
    rw [Matrix.trace_fin_two, RCLike.re_to_complex, Complex.add_re]
    rfl
  have hsum : a + b = X 0 + X 1 := by
    have h := congrArg RCLike.re hH.trace_eq_sum_eigenvalues
    rw [Fin.sum_univ_two, map_add, RCLike.ofReal_re, RCLike.ofReal_re, htrace] at h
    exact h.symm
  have hdet0 : 0 < ‖((g : Matrix (Fin 2) (Fin 2) ℂ)).det‖ :=
    norm_pos_iff.mpr (Minkowski.det_ne_zero g)
  have htr : ‖((g : Matrix (Fin 2) (Fin 2) ℂ)).det‖ * (a + b) =
      ∑ i : Fin 2, ∑ j : Fin 2, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ^ 2 := by
    rw [hsum, hXdef, conjAct_origin_zero, conjAct_origin_one, ← mul_add, ← mul_assoc,
      mul_inv_cancel₀ hdet0.ne', one_mul,
      Fin.sum_univ_two (fun i ↦ ∑ j : Fin 2, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ^ 2)]
  have hnonneg : 0 ≤ a + b := by
    have h0 : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ^ 2 :=
      Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _
    rw [← htr] at h0
    exact (mul_nonneg_iff_of_pos_left hdet0).mp h0
  have ha : 0 < a := by
    by_contra hcon
    push Not at hcon
    have hb : b < 0 := by
      by_contra hb'
      push Not at hb'
      nlinarith
    nlinarith
  have hb : 0 < b := by nlinarith
  refine ⟨U, a, b, hUmem, ha, hb, hab, htr, ?_⟩
  apply herm_injective
  rw [herm_conjAct U (diagPoint a b), herm_diagPoint, norm_det_of_mem_unitary hUmem, inv_one,
    one_smul, hUcoe]
  exact hspec

/-! ## For every `g` -/

/-- **The walls separating the base point from its `g`-translate**: finite shell measure, at least
`2φ(1)·|log a|` for the eigenvalue `a` of `g g*/|det g|`, where `|det g|(a + a⁻¹) = Σ |g_ij|²`. -/
theorem separation_bound (g : GL (Fin 2) ℂ) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a * b = 1 ∧
      ‖((g : Matrix (Fin 2) (Fin 2) ℂ)).det‖ * (a + b) =
        ∑ i : Fin 2, ∑ j : Fin 2, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ^ 2 ∧
      shellMeasure (symmDiff (posSide origin) (posSide (conjAct g origin))) < ⊤ ∧
      2 * wedgePhi 1 * |Real.log a| ≤
        (shellMeasure (symmDiff (posSide origin) (posSide (conjAct g origin)))).toReal := by
  obtain ⟨U, a, b, hU, ha, hb, hab, htr, hX⟩ := exists_unitary_diagPoint g
  refine ⟨a, b, ha, hb, hab, htr, ?_, ?_⟩
  · rw [hX, shellMeasure_symmDiff_conjAct_unitary hU]
    exact shellMeasure_symmDiff_diagPoint_lt_top ha hb
  · rw [hX, shellMeasure_symmDiff_conjAct_unitary hU]
    have h := volume_diagonal_sep_ge ha hab
    linarith

/-- **Both differences of the half-spaces have finite shell measure**, for every `g`. -/
theorem separation_diff_lt_top (g : GL (Fin 2) ℂ) :
    shellMeasure (posSide (conjAct g origin) \ posSide origin) < ⊤ ∧
      shellMeasure (posSide origin \ posSide (conjAct g origin)) < ⊤ := by
  obtain ⟨_a, _b, -, -, -, -, hfin, -⟩ := separation_bound g
  refine ⟨(measure_mono fun v hv ↦ ?_).trans_lt hfin, (measure_mono fun v hv ↦ ?_).trans_lt hfin⟩
  · exact Set.mem_symmDiff.mpr (Or.inr hv)
  · exact Set.mem_symmDiff.mpr (Or.inl hv)

end

end Wedge
end GHW
end GroupApproximation

open GroupApproximation.GHW.Wedge

#audit_axioms exists_unitary_diagPoint
#audit_axioms shellMeasure_symmDiff_conjAct_unitary
#audit_axioms volume_diagonal_sep_ge
#audit_axioms separation_bound
#audit_axioms separation_diff_lt_top
