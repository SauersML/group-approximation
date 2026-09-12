import GroupApproximation.CharClass.LIXKGenBaseChart
import GroupApproximation.CharClass.LIXKGenBundle
import GroupApproximation.CharClass.LIXHsqEta
import GroupApproximation.Meta.AxiomGuard

/-!
# The `k`-section at the `i`-th zero is a fixed linear function of the chart's value, at rank `n`

Lane `lix-oddside` (lead ruling 2026-09-11: leaf (3) of the `k`-zero Step C data, the rank-`n`
port of `CharClass/LIXHsqEta.lean`).

At a chart point `q` of the base chart at the `i`-th zero, `lixKBaseChart n k dd i`, the sphere
coordinate is `chartZeroVec n k i w`, and `Ψ_k` of it is the chart at `−e₀`
(`psiVec_chartZeroVec`).  So the southern field of the `k`-section, read in that chart, is the
one-zero expression at `−e₀`: `lixKEtaLin n q (lixKProductChart n dd q)`, independent of `i`.
Only the frame of the mapping torus depends on `i`.

## Main definitions

* `lixKTau` — the path parameter at a chart point.
* `lixKEtaLin` — **the reconstruction**, linear in its second argument only.

## Main results

* `lixKEtaLin_eq_blockSouth` — it reproduces the southern field of the `k`-section at every zero.
* `lixKSection_eq_mulVec` — hence the section itself, on the ball.
* `Vmat_mulVec_lixKEtaLin` — its values lie in the fibre of `V`.
* `lixKEtaLin_eq_zero_iff` — it is injective.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open scoped Matrix
open Set
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The path parameter -/

/-- The manuscript path's parameter at a chart point. -/
def lixKTau (n : ℕ) (q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) : ℝ :=
  southParam circHoriz (circChartFun q.1.2)

theorem lixKTau_eq (n : ℕ) {q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)}
    (hu : q.1.2 ∈ Ioo (-1 : ℝ) 1) : lixKTau n q = (1 + q.1.2) / 2 := by
  rw [lixKTau, southParam, circHoriz_circChartFun hu]

theorem lixKTau_mem (n : ℕ) {q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)}
    (hu : q.1.2 ∈ Ioo (-1 : ℝ) 1) : lixKTau n q ∈ Ioo (0 : ℝ) 1 := by
  rw [lixKTau_eq n hu]
  constructor
  · linarith [hu.1]
  · linarith [hu.2]

/-- **The path's weight is strictly positive on the ball.** -/
theorem lixChi_lixKTau_pos (n : ℕ) {q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)}
    (hu : q.1.2 ∈ Ioo (-1 : ℝ) 1) : 0 < lixChi (lixKTau n q) := by
  have h := lixKTau_mem n hu
  rw [lixChi]
  refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
  · exact mul_pos Real.pi_pos h.1
  · nlinarith [Real.pi_pos, h.2]

/-! ## 2. The reconstruction -/

/-- **The section's blocks, as a linear function of the chart's coordinates.** -/
def lixKEtaLin (n : ℕ) (q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
    (ab : (Fin (n + 1) → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) : Gen.VIdx n dd → ℂ :=
  Sum.elim ab.1 fun h : HIdx dd =>
    ((lixChi (lixKTau n q) : ℝ) : ℂ) * ab.2 h.1.1 h.1.2 * CPn.chartVec (q.2 h.1.1) h.2

@[simp] theorem lixKEtaLin_inl (n : ℕ) (q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
    (ab : (Fin (n + 1) → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) (a : Fin (n + 1)) :
    lixKEtaLin n q ab (Sum.inl a) = ab.1 a := rfl

@[simp] theorem lixKEtaLin_inr (n : ℕ) (q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
    (ab : (Fin (n + 1) → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) (h : HIdx dd) :
    lixKEtaLin n q ab (Sum.inr h)
      = ((lixChi (lixKTau n q) : ℝ) : ℂ) * ab.2 h.1.1 h.1.2
        * CPn.chartVec (q.2 h.1.1) h.2 := rfl

/-- **The reconstruction reproduces the southern field of the `k`-section at the `i`-th zero.** -/
theorem lixKEtaLin_eq_blockSouth (n k : ℕ) (i : Fin (k + 1))
    {q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)}
    (hu : q.1.2 ∈ Ioo (-1 : ℝ) 1) (hsq : chartQ n q.1.1 ≤ 1) :
    lixKEtaLin n q (lixKProductChart n dd q)
      = blockSouth (aVecK n) (bVecK n k) (fun m => Gen.cVec m.2) lixChi circHoriz
          (lixKBaseChart n k dd i q) := by
  have hprod : lixKProductChart n dd q = (eulerLocalHomeo n q.1, cpLocalHomeo dd q.2) := rfl
  have hcp : (cpLocalHomeo dd : (∀ j : Fin ℓ, Fin (dd j) → ℂ) → _) = cpChartSectionPi dd :=
    hasStrictFDerivAt_cpChartSectionPi.toOpenPartialHomeomorph_coe
  have heu : (eulerLocalHomeo n : ChartSrc n → (Fin (n + 1) → ℂ))
      = fun p => trivialBlockChart n p.1 p.2 := eulerLocalHomeo_coe n
  funext x
  cases x with
  | inl a =>
      rw [hprod, lixKEtaLin_inl]
      show eulerLocalHomeo n q.1 a
        = ((1 - lixKTau n q : ℝ) : ℂ) * (Sum.elim (aVecK n (lixKBaseChart n k dd i q).2)
              (0 : HIdx dd → ℂ) (Sum.inl a))
          + ((lixKTau n q : ℝ) : ℂ) * (Sum.elim (bVecK n k (lixKBaseChart n k dd i q).2)
              (0 : HIdx dd → ℂ) (Sum.inl a))
          + ((lixChi (lixKTau n q) : ℝ) : ℂ) * (Sum.elim (0 : Fin (n + 1) → ℂ)
              (Gen.cVec (lixKBaseChart n k dd i q).2.2) (Sum.inl a))
      rw [Sum.elim_inl, Sum.elim_inl, Sum.elim_inl, heu, lixKTau_eq n hu]
      show trivialBlockChart n q.1.1 q.1.2 a
        = ((1 - (1 + q.1.2) / 2 : ℝ) : ℂ) * eZero n a
          + (((1 + q.1.2) / 2 : ℝ) : ℂ) * psiVec n k (chartZeroVec n k i (chartClamp n q.1.1)) a
          + ((lixChi ((1 + q.1.2) / 2) : ℝ) : ℂ) * (0 : Fin (n + 1) → ℂ) a
      rw [chartClamp_eq_self hsq, psiVec_chartZeroVec]
      show ((1 - (1 + q.1.2) / 2 : ℝ) : ℂ) * eZero n a
          + (((1 + q.1.2) / 2 : ℝ) : ℂ) * sphereChartVec n q.1.1 a = _
      simp
  | inr h =>
      rw [hprod, lixKEtaLin_inr]
      show ((lixChi (lixKTau n q) : ℝ) : ℂ) * (cpLocalHomeo dd q.2) h.1.1 h.1.2
            * CPn.chartVec (q.2 h.1.1) h.2
        = ((1 - lixKTau n q : ℝ) : ℂ) * (Sum.elim (aVecK n (lixKBaseChart n k dd i q).2)
              (0 : HIdx dd → ℂ) (Sum.inr h))
          + ((lixKTau n q : ℝ) : ℂ) * (Sum.elim (bVecK n k (lixKBaseChart n k dd i q).2)
              (0 : HIdx dd → ℂ) (Sum.inr h))
          + ((lixChi (lixKTau n q) : ℝ) : ℂ) * (Sum.elim (0 : Fin (n + 1) → ℂ)
              (Gen.cVec (lixKBaseChart n k dd i q).2.2) (Sum.inr h))
      rw [Sum.elim_inr, Sum.elim_inr, Sum.elim_inr, hcp]
      show ((lixChi (lixKTau n q) : ℝ) : ℂ) * cpChartSection (q.2 h.1.1) h.1.2
            * CPn.chartVec (q.2 h.1.1) h.2
        = ((1 - lixKTau n q : ℝ) : ℂ) * (0 : HIdx dd → ℂ) h
          + ((lixKTau n q : ℝ) : ℂ) * (0 : HIdx dd → ℂ) h
          + ((lixChi (lixKTau n q) : ℝ) : ℂ) * Gen.cVec (lixKBaseChart n k dd i q).2.2 h
      rw [Gen.cVec_apply]
      show ((lixChi (lixKTau n q) : ℝ) : ℂ) * cpChartSection (q.2 h.1.1) h.1.2
            * CPn.chartVec (q.2 h.1.1) h.2
        = _ + _ + ((lixChi (lixKTau n q) : ℝ) : ℂ)
            * CPn.entry (CPn.chartAt (q.2 h.1.1)) h.2 h.1.2.succ
      rw [chartAt_entry_succ_eq]
      simp
      ring

/-! ## 3. What the reconstruction is good for -/

/-- **The `k`-section on the ball at the `i`-th zero, in reconstructed form.** -/
theorem lixKSection_eq_mulVec (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    {q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)}
    (hu : q.1.2 ∈ Ioo (-1 : ℝ) 1) (hsq : chartQ n q.1.1 ≤ 1) :
    lixKSection n k G (lixKBaseChart n k dd i q)
      = mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKBaseChart n k dd i q)
          *ᵥ Sum.elim 0 (lixKEtaLin n q (lixKProductChart n dd q)) := by
  have hneg : ¬ (0 : ℝ) ≤ circHeight (lixKBaseChart n k dd i q).1 := by
    have := circHeight_circChartFun_neg hu
    show ¬ (0 : ℝ) ≤ circHeight (circChartFun q.1.2)
    linarith
  rw [lixKSection, mtSection, if_neg hneg, lixKEtaLin_eq_blockSouth n k i hu hsq]

/-- **The reconstruction lands in the fibre of `V`.** -/
theorem Vmat_mulVec_lixKEtaLin (n k : ℕ) (i : Fin (k + 1))
    (q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
    (ab : (Fin (n + 1) → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) :
    Gen.Vmat n (lixKBaseChart n k dd i q).2 *ᵥ lixKEtaLin n q ab = lixKEtaLin n q ab := by
  funext x
  cases x with
  | inl a =>
      show (Matrix.fromBlocks 1 0 0 (Gen.Hmat (lixKBaseChart n k dd i q).2.2)
        *ᵥ Sum.elim (fun a => lixKEtaLin n q ab (Sum.inl a))
            (fun h => lixKEtaLin n q ab (Sum.inr h))) (Sum.inl a) = _
      rw [Matrix.fromBlocks_mulVec]
      show (1 *ᵥ fun a => lixKEtaLin n q ab (Sum.inl a)) a
          + (0 *ᵥ fun h => lixKEtaLin n q ab (Sum.inr h)) a = _
      rw [Matrix.one_mulVec, Matrix.zero_mulVec]
      simp
  | inr h =>
      show (Matrix.fromBlocks 1 0 0 (Gen.Hmat (lixKBaseChart n k dd i q).2.2)
        *ᵥ Sum.elim (fun a => lixKEtaLin n q ab (Sum.inl a))
            (fun h => lixKEtaLin n q ab (Sum.inr h))) (Sum.inr h) = _
      rw [Matrix.fromBlocks_mulVec]
      show (0 *ᵥ fun a => lixKEtaLin n q ab (Sum.inl a)) h
          + (Gen.Hmat (lixKBaseChart n k dd i q).2.2 *ᵥ fun h => lixKEtaLin n q ab (Sum.inr h)) h
          = _
      rw [Matrix.zero_mulVec, Gen.Hmat, blockDiagonal'_mulVec]
      show (0 : HIdx dd → ℂ) h
          + ∑ k', CPn.entry (CPn.chartAt (q.2 h.1.1)) h.2 k'
              * (((lixChi (lixKTau n q) : ℝ) : ℂ) * ab.2 h.1.1 h.1.2
                * CPn.chartVec (q.2 h.1.1) k') = _
      have hcol : ∀ k' : Fin (dd h.1.1 + 1),
          CPn.entry (CPn.chartAt (q.2 h.1.1)) h.2 k'
              * (((lixChi (lixKTau n q) : ℝ) : ℂ) * ab.2 h.1.1 h.1.2
                * CPn.chartVec (q.2 h.1.1) k')
            = (((lixChi (lixKTau n q) : ℝ) : ℂ) * ab.2 h.1.1 h.1.2)
              * (CPn.entry (CPn.chartAt (q.2 h.1.1)) h.2 k'
                * CPn.chartVec (q.2 h.1.1) k') := by
        intro k'; ring
      rw [Finset.sum_congr rfl fun k' _ => hcol k', ← Finset.mul_sum]
      have hfix : ∑ k', CPn.entry (CPn.chartAt (q.2 h.1.1)) h.2 k'
          * CPn.chartVec (q.2 h.1.1) k' = CPn.chartVec (q.2 h.1.1) h.2 := by
        have hD : ((CPn.sqNorm (CPn.chartVec (q.2 h.1.1)) : ℝ) : ℂ) ≠ 0 :=
          CPn.chartDenom_ne_zero _
        have hterm : ∀ k' : Fin (dd h.1.1 + 1),
            CPn.entry (CPn.chartAt (q.2 h.1.1)) h.2 k' * CPn.chartVec (q.2 h.1.1) k'
              = CPn.chartVec (q.2 h.1.1) h.2
                * (star (CPn.chartVec (q.2 h.1.1) k') * CPn.chartVec (q.2 h.1.1) k')
                / ((CPn.sqNorm (CPn.chartVec (q.2 h.1.1)) : ℝ) : ℂ) := by
          intro k'
          rw [CPn.chartAt_entry]
          ring
        rw [Finset.sum_congr rfl fun k' _ => hterm k', ← Finset.sum_div, ← Finset.mul_sum]
        have hsum : ∑ k' : Fin (dd h.1.1 + 1),
            star (CPn.chartVec (q.2 h.1.1) k') * CPn.chartVec (q.2 h.1.1) k'
              = ((CPn.sqNorm (CPn.chartVec (q.2 h.1.1)) : ℝ) : ℂ) := by
          rw [CPn.sqNorm]
          push_cast
          refine Finset.sum_congr rfl fun k' _ => ?_
          exact RCLike.conj_mul (CPn.chartVec (q.2 h.1.1) k')
        rw [hsum]
        field_simp
      rw [hfix]
      show (0 : ℂ) + _ = _
      rw [zero_add, lixKEtaLin_inr]

/-- **The reconstruction is injective.** -/
theorem lixKEtaLin_eq_zero_iff (n : ℕ) {q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)}
    (hu : q.1.2 ∈ Ioo (-1 : ℝ) 1)
    (ab : (Fin (n + 1) → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) :
    lixKEtaLin n q ab = 0 ↔ ab = 0 := by
  constructor
  · intro h
    have hchi : ((lixChi (lixKTau n q) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (lixChi_lixKTau_pos n hu).ne'
    refine Prod.ext ?_ ?_
    · funext a
      have := congrFun h (Sum.inl a)
      rw [lixKEtaLin_inl] at this
      simpa using this
    · funext j x
      have := congrFun h (Sum.inr ⟨⟨j, x⟩, 0⟩)
      rw [lixKEtaLin_inr] at this
      simp only [chartVec_zero_eq_one, mul_one] at this
      have h2 : ab.2 j x = 0 := by
        rcases mul_eq_zero.mp this with h3 | h3
        · exact absurd h3 hchi
        · exact h3
      simpa using h2
  · intro h
    subst h
    funext x
    cases x with
    | inl a => simp [lixKEtaLin_inl]
    | inr h => simp [lixKEtaLin_inr]

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.lixKSection_eq_mulVec
#audit_axioms KGen.Vmat_mulVec_lixKEtaLin
#audit_axioms KGen.lixKEtaLin_eq_zero_iff

end GroupApproximation.CharClass
