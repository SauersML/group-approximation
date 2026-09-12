import GroupApproximation.Analysis.LIXPowersEquator

/-!
# The suspension chart of `S^{2n+1}`, and `Σψ_k` as an honest self-map

`Analysis/LIXPowersNaturality.lean`'s `clutchMat_comp_radial_pullback` transports the
projection clutched by `Ω ∘ Ψ` to the projection clutched by `Ω` read at `Φ x`, for any
realisation `Φ` of the suspension `ΣΨ` on a parameter space carrying a suspension chart
`(t, ν)`.  This file supplies the concrete data at rank `n`:

* the parameter space is the unit sphere `STW59.unitVectors (Fin (n+1))` of `ℂ^{n+1}`;
* the clutching coordinate is `chartHeight n x = Re (x (Fin.last n))`;
* the equatorial part is `chartEquator n x = equatorProj n x ∈ E n`, the real coordinates
  `Gen.equatorEmb n` reads (`equatorEmb_equatorProj`), and `isSuspensionChart_unitVectors`
  says the pair is a suspension chart;
* `Φ = psiUnit n k` is `KGen.psiVec n k` on the unit sphere, spelled `psiUpdate` here without
  the `CharClass` import; it fixes the height (`psiUnit_height`) and moves the equatorial part
  by the join power (`psiUnit_equator`).

With those, `clutchMat_comp_joinPow_psiUnit` is the naturality statement at rank `n`.  This is
the clutched route, off the critical path of the powers chain; it is here so that the
naturality lemma has a concrete instance.
-/

namespace GroupApproximation
namespace LIX
namespace Powers

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

/-! ## The equatorial part of a vector of `ℂ^{n+1}` -/

section Chart

variable (n : ℕ)

/-- The real coordinates of `x ∈ ℂ^{n+1}` that the equator embedding reads: the real and
imaginary parts of the first `n` complex coordinates, and the imaginary part of the last. -/
def equatorProjFun (x : Fin (n + 1) → ℂ) : (Fin n × Fin 2) ⊕ Unit → ℝ
  | Sum.inl (i, b) => if (b : ℕ) = 0 then (x i.castSucc).re else (x i.castSucc).im
  | Sum.inr _ => (x (Fin.last n)).im

/-- **The equatorial part of `x`**, as a point of `E n`. -/
def equatorProj (x : Fin (n + 1) → ℂ) : EuclideanSpace ℝ (Fin (2 * n + 1)) :=
  WithLp.toLp 2 fun j => equatorProjFun n x (Gen.eqBwd n j)

theorem equatorProj_eqFwd (x : Fin (n + 1) → ℂ) (s : (Fin n × Fin 2) ⊕ Unit) :
    equatorProj n x (Gen.eqFwd n s) = equatorProjFun n x s := by
  simp only [equatorProj, PiLp.toLp_apply, Gen.eqBwd_eqFwd]

/-- The equator embedding of the equatorial part forgets the real part of the last
coordinate. -/
theorem equatorEmb_equatorProj (x : Fin (n + 1) → ℂ) :
    Gen.equatorEmb n (equatorProj n x)
      = Function.update x (Fin.last n) (((x (Fin.last n)).im : ℂ) * Complex.I) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · rw [Function.update_self, Gen.equatorEmb_last, equatorProj_eqFwd]
    rfl
  · intro i
    rw [Function.update_of_ne (Fin.castSucc_lt_last i).ne, Gen.equatorEmb_castSucc,
      equatorProj_eqFwd, equatorProj_eqFwd]
    show ((x i.castSucc).re : ℂ) + ((x i.castSucc).im : ℂ) * Complex.I = x i.castSucc
    exact Complex.re_add_im _

/-- **The sphere relation**: the equatorial part and the clutching coordinate together carry
the whole norm. -/
theorem norm_sq_equatorProj_add (x : Fin (n + 1) → ℂ) :
    ‖equatorProj n x‖ ^ 2 + (x (Fin.last n)).re ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  have hl : ‖(((x (Fin.last n)).im : ℂ) * Complex.I)‖ ^ 2 + (x (Fin.last n)).re ^ 2
      = ‖x (Fin.last n)‖ ^ 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hc : ∀ i : Fin n,
      Function.update x (Fin.last n) (((x (Fin.last n)).im : ℂ) * Complex.I) i.castSucc
        = x i.castSucc :=
    fun i => Function.update_of_ne (Fin.castSucc_lt_last i).ne _ _
  rw [← Gen.sum_norm_sq_equatorEmb, equatorEmb_equatorProj, Fin.sum_univ_castSucc,
    Fin.sum_univ_castSucc, Function.update_self]
  simp only [hc]
  linarith [hl]

theorem continuous_equatorProj : Continuous (equatorProj n) := by
  show Continuous fun x : Fin (n + 1) → ℂ =>
    WithLp.toLp 2 fun j => equatorProjFun n x (Gen.eqBwd n j)
  refine (PiLp.continuous_toLp ..).comp ?_
  refine continuous_pi fun j => ?_
  generalize Gen.eqBwd n j = s
  rcases s with ⟨i, b⟩ | ⟨⟩
  · by_cases hb : (b : ℕ) = 0
    · simp only [equatorProjFun, if_pos hb]
      exact Complex.continuous_re.comp (continuous_apply i.castSucc)
    · simp only [equatorProjFun, if_neg hb]
      exact Complex.continuous_im.comp (continuous_apply i.castSucc)
  · simp only [equatorProjFun]
    exact Complex.continuous_im.comp (continuous_apply (Fin.last n))

/-- The equator embedding is injective. -/
theorem equatorEmb_injective : Function.Injective (Gen.equatorEmb n) := by
  intro a b hab
  refine PiLp.ext fun j => ?_
  rw [← Gen.eqFwd_eqBwd n j]
  generalize Gen.eqBwd n j = s
  rcases s with ⟨i, c⟩ | ⟨⟩
  · have h := congrFun hab i.castSucc
    rw [Gen.equatorEmb_castSucc, Gen.equatorEmb_castSucc] at h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp at hre him
    fin_cases c
    · exact hre
    · exact him
  · have h := congrFun hab (Fin.last n)
    rw [Gen.equatorEmb_last, Gen.equatorEmb_last] at h
    have him := congrArg Complex.im h
    simpa using him

/-- The clutching coordinate of a unit vector of `ℂ^{n+1}`. -/
def chartHeight (x : ↥(STW59.unitVectors (Fin (n + 1)))) : ℝ :=
  ((x : Fin (n + 1) → ℂ) (Fin.last n)).re

/-- The equatorial part of a unit vector of `ℂ^{n+1}`. -/
def chartEquator (x : ↥(STW59.unitVectors (Fin (n + 1)))) :
    EuclideanSpace ℝ (Fin (2 * n + 1)) :=
  equatorProj n (x : Fin (n + 1) → ℂ)

/-- **`S^{2n+1}` with the clutching coordinate `Re x_last` is a suspension chart over
`E n`.** -/
theorem isSuspensionChart_unitVectors :
    IsSuspensionChart (chartHeight n) (chartEquator n) where
  continuous_height :=
    (Complex.continuous_re.comp (continuous_apply (Fin.last n))).comp continuous_subtype_val
  continuous_equator := (continuous_equatorProj n).comp continuous_subtype_val
  sphere := fun x => by
    rw [chartEquator, chartHeight, norm_sq_equatorProj_add]
    exact STW59.mem_unitVectors_iff.mp x.2

end Chart

/-! ## `Σψ_k` on the unit sphere -/

section Psi

variable (n : ℕ)

/-- `KGen.psiVec n k` on `ℂ^{n+1}`, spelled without the `CharClass` import. -/
def psiUpdate (k : ℕ) (x : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  Function.update x 0 (joinC k (x 0))

theorem sum_norm_sq_psiUpdate (k : ℕ) (x : Fin (n + 1) → ℂ) :
    ∑ i, ‖psiUpdate n k x i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_ne i 0 with rfl | hi
  · rw [psiUpdate, Function.update_self, norm_joinC]
  · rw [psiUpdate, Function.update_of_ne hi]

/-- **`Σψ_k` as a self-map of `S^{2n+1}`.** -/
def psiUnit (k : ℕ) (x : ↥(STW59.unitVectors (Fin (n + 1)))) :
    ↥(STW59.unitVectors (Fin (n + 1))) :=
  ⟨psiUpdate n k x, by
    rw [STW59.mem_unitVectors_iff, sum_norm_sq_psiUpdate]
    exact STW59.mem_unitVectors_iff.mp x.2⟩

/-- `Σψ_k` fixes the clutching coordinate. -/
theorem psiUnit_height (hn : 0 < n) (k : ℕ) (x : ↥(STW59.unitVectors (Fin (n + 1)))) :
    chartHeight n (psiUnit n k x) = chartHeight n x := by
  show (psiUpdate n k (x : Fin (n + 1) → ℂ) (Fin.last n)).re
    = ((x : Fin (n + 1) → ℂ) (Fin.last n)).re
  rw [psiUpdate, Function.update_of_ne (last_ne_zero_of_pos n hn)]

/-- `KGen.psiVec n k` moves the equatorial part by the join power. -/
theorem equatorProj_psiUpdate (hn : 0 < n) (k : ℕ) (x : Fin (n + 1) → ℂ) :
    equatorProj n (psiUpdate n k x)
      = joinPow (eqBasis n hn 0) (eqBasis n hn 1) k (equatorProj n x) := by
  have h0 : (0 : Fin (n + 1)) ≠ Fin.last n := (last_ne_zero_of_pos n hn).symm
  apply equatorEmb_injective n
  rw [equatorEmb_joinPow, equatorEmb_equatorProj, equatorEmb_equatorProj, psiUpdate,
    Function.update_of_ne (last_ne_zero_of_pos n hn), Function.update_of_ne h0,
    Function.update_comm h0]

/-- `Σψ_k` moves the equatorial part by the join power. -/
theorem psiUnit_equator (hn : 0 < n) (k : ℕ) (x : ↥(STW59.unitVectors (Fin (n + 1)))) :
    chartEquator n (psiUnit n k x)
      = joinPow (eqBasis n hn 0) (eqBasis n hn 1) k (chartEquator n x) :=
  equatorProj_psiUpdate n hn k x

/-- **Naturality of clutching along `Σψ_k` on `S^{2n+1}`**: the projection clutched by
`Ω ∘ ψ_k` at `x` is the projection clutched by `Ω` at `Σψ_k x`. -/
theorem clutchMat_comp_joinPow_psiUnit (hn : 0 < n) (k : ℕ) {m : Type*} [Fintype m]
    [DecidableEq m] (Ω : EuclideanSpace ℝ (Fin (2 * n + 1)) → Matrix m m ℂ)
    (x : ↥(STW59.unitVectors (Fin (n + 1)))) :
    clutchMat (chartHeight n x)
        (coneMat (fun z => Ω (joinPow (eqBasis n hn 0) (eqBasis n hn 1) k z)) (chartEquator n x))
      = clutchMat (chartHeight n (psiUnit n k x)) (coneMat Ω (chartEquator n (psiUnit n k x))) :=
  clutchMat_comp_radial_pullback (isRadialMap_joinPow_equator n hn k) Ω
    (psiUnit_height n hn k) (psiUnit_equator n hn k) x

end Psi

end

end Powers
end LIX
end GroupApproximation
