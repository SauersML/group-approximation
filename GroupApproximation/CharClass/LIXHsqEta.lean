import GroupApproximation.CharClass.LIXHsqNeighbourhood
import GroupApproximation.CharClass.LIXProductChart
import GroupApproximation.CharClass.LemmaTwoGlue
import GroupApproximation.Meta.AxiomGuard

/-!
# The section is a fixed linear function of the chart's *value*, at each chart point

Lane `lix-hsq`.

The comparison homotopy of `hsq` contracts a chart-coordinate point `q` to the origin while
holding the **chart's reading of the section** fixed.  For that to be a homotopy of maps of
pairs, and for its far end to be a linear map, the section must be recoverable from the
chart's value by a map that is linear in that value and depends only continuously on `q`.
It is, and `lixEtaLin` is that map.

## What is linear here, and what is not

`lixEtaLin q ab` is linear in `ab` — **the chart's value** — for each fixed `q`.  Read it as
a family of linear maps indexed by the point, not as a linear map of the point.

Three things are **not** linear, and confusing any of them with the above would make this
file's role in `hsq` a fiction:

* `q ↦ lixEtaLin q ab` is not linear.  The coefficients are `χ(τ q)` and `chartVec (q.2 j)`,
  neither of which is linear in `q`.
* The section in coordinates, `q ↦ lixEtaLin q (lixProductChart dd q)`, is not linear
  either — in the trivial block it **is** `eulerLocalHomeo`, which is the inverse-function-
  theorem local homeomorphism `fun p => trivialBlockChart p.1 p.2`, honestly nonlinear;
  what is linear is only its *derivative* at the zero, `eulerContinuousLinearEquiv`.
* The transverse block, as a function of the base coordinate, is a product of two
  `wⱼ`-dependent factors and so is not even affine in it.

Linearity is consumed at exactly one place downstream: `LIXHsqLinear.lixEtaZeroMap`, the
specialisation `q = 0`, where the base is pinned at the section's zero and only the second
argument moves.  Nothing in `hsq` needs `q ↦ ⋯` to be linear, and nothing claims it is.

## The two blocks

* The trivial block of the section, read in the charts, is `eulerLocalHomeo` applied to the
  point — that is what `LIXSectionChart.trivialBlockChart` is — and the identification is a
  matter of unfolding once the two clamps are inactive (`LIXHsqNeighbourhood`'s cap).
* The transverse block is `cVec`, the `(i+1)`-st column of the `j`-th projection.  In the
  affine chart that column is `chartVec (wⱼ) * conj (wⱼ)ᵢ / (1 + ‖wⱼ‖²)`
  (`tautColSection_chartAt`), i.e. the chart coordinate `cpChartSection (wⱼ)ᵢ` **times the
  vector `chartVec wⱼ`**.  So it is linear in the chart's value, with a coefficient that
  depends — nonlinearly — on the base point.

The path's weight `χ(τ)` multiplies the transverse block and is carried in the coefficient
too; it is strictly positive on the ball, which is why the reconstruction stays injective.

**Nothing here is the nondegeneracy of the zero.**  That was paid for once, when
`lixProductChart` was built from the inverse function theorem, and this file only says that
the chart's value determines the section linearly — the statement that makes the
nondegeneracy reusable at every point of the contraction rather than at the zero alone.

## Main definitions

* `lixTau` — the path parameter at a chart point.
* `lixEtaLin` — **the reconstruction**, linear in its second argument only.

## Main results

* `lixEtaLin_eq_blockSouth` — it reproduces the manuscript's southern field.
* `lixSection_eq_mulVec` — hence the section itself, on the ball.
* `Vmat_mulVec_lixEtaLin` — its values lie in the fibre of `V`.
* `lixEtaLin_eq_zero_iff` — it is injective.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open Set
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

/-! ## 1. The circle coordinate, read back -/

theorem circHoriz_circChartFun {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    circHoriz (circChartFun u) = u := by
  show (circChartVec (circClamp u) : EuclideanSpace ℝ (Fin 2)) 0 = u
  rw [circClamp_eq_self hu]
  simp [circChartVec]

theorem circHeight_circChartFun_neg {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    circHeight (circChartFun u) < 0 := by
  show (circChartVec (circClamp u) : EuclideanSpace ℝ (Fin 2)) 1 < 0
  rw [circClamp_eq_self hu]
  have h1 : (0 : ℝ) < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have h2 : Real.sqrt (1 - u ^ 2) > 0 := Real.sqrt_pos.mpr h1
  simpa [circChartVec] using h2

/-! ## 2. The path parameter -/

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- The manuscript path's parameter at a chart point. -/
def lixTau (q : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) : ℝ :=
  southParam circHoriz (circChartFun q.1.2)

theorem lixTau_eq {q : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)}
    (hu : q.1.2 ∈ Ioo (-1 : ℝ) 1) : lixTau q = (1 + q.1.2) / 2 := by
  rw [lixTau, southParam, circHoriz_circChartFun hu]

theorem lixTau_mem {q : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)}
    (hu : q.1.2 ∈ Ioo (-1 : ℝ) 1) : lixTau q ∈ Ioo (0 : ℝ) 1 := by
  rw [lixTau_eq hu]
  constructor
  · linarith [hu.1]
  · linarith [hu.2]

/-- **The path's weight is strictly positive on the ball.**  It is `sin (π τ)` and `τ` lies
strictly between `0` and `1`; at the origin it is `1`. -/
theorem lixChi_lixTau_pos {q : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)}
    (hu : q.1.2 ∈ Ioo (-1 : ℝ) 1) : 0 < lixChi (lixTau q) := by
  have h := lixTau_mem hu
  rw [lixChi]
  refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
  · exact mul_pos Real.pi_pos h.1
  · nlinarith [Real.pi_pos, h.2]

/-! ## 3. The projective column, in the chart -/

/-- **A column of the projection is its chart coordinate times `chartVec`.**  The `(i+1)`-st
column of `chartAt w` is `conj (wᵢ)/(1 + ‖w‖²)` times the vector `(1, w)`, and the first
factor is exactly `cpChartSection w i`. -/
theorem chartAt_entry_succ_eq {d : ℕ} (w : Fin d → ℂ) (k : Fin (d + 1)) (i : Fin d) :
    CPn.entry (CPn.chartAt w) k i.succ = cpChartSection w i * CPn.chartVec w k := by
  rw [CPn.chartAt_entry, CPn.chartVec_succ, CPn.chartVec_sqNorm]
  show CPn.chartVec w k * star (w i) / (((1 : ℝ) + ∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ)
    = star (w i) / (((1 : ℝ) + ∑ k, ‖w k‖ ^ 2 : ℝ) : ℂ) * CPn.chartVec w k
  ring

/-- The `0`-th entry of `chartVec` is `1`; recorded here because injectivity of the
reconstruction reads the transverse block at exactly that entry. -/
theorem chartVec_zero_eq_one {d : ℕ} (w : Fin d → ℂ) : CPn.chartVec w 0 = 1 :=
  CPn.chartVec_zero w

/-! ## 4. The reconstruction -/

/-- **The section's blocks, as a linear function of the chart's coordinates.**  The trivial
block is read off, and the transverse block is the chart coordinate scaled by the path's
weight and by the base point's own lift `chartVec`. -/
def lixEtaLin (q : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
    (ab : (Fin 3 → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) : VIdx dd → ℂ :=
  Sum.elim ab.1 fun h : HIdx dd =>
    ((lixChi (lixTau q) : ℝ) : ℂ) * ab.2 h.1.1 h.1.2 * CPn.chartVec (q.2 h.1.1) h.2

@[simp] theorem lixEtaLin_inl (q : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
    (ab : (Fin 3 → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) (k : Fin 3) :
    lixEtaLin q ab (Sum.inl k) = ab.1 k := rfl

@[simp] theorem lixEtaLin_inr (q : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
    (ab : (Fin 3 → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) (h : HIdx dd) :
    lixEtaLin q ab (Sum.inr h)
      = ((lixChi (lixTau q) : ℝ) : ℂ) * ab.2 h.1.1 h.1.2
        * CPn.chartVec (q.2 h.1.1) h.2 := rfl

/-- **The reconstruction reproduces the manuscript's southern field.** -/
theorem lixEtaLin_eq_blockSouth {q : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)}
    (hu : q.1.2 ∈ Ioo (-1 : ℝ) 1) (hsq : sphereQ q.1.1 ≤ 1) :
    lixEtaLin q (lixProductChart dd q)
      = blockSouth aVec bVec cVec lixChi circHoriz (lixBaseChartFun dd q) := by
  have hprod : lixProductChart dd q = (eulerLocalHomeo q.1, cpLocalHomeo dd q.2) := rfl
  have hcp : (cpLocalHomeo dd : (∀ j : Fin ℓ, Fin (dd j) → ℂ) → _) = cpChartSectionPi dd :=
    hasStrictFDerivAt_cpChartSectionPi.toOpenPartialHomeomorph_coe
  have heu : (eulerLocalHomeo : ChartSrc → (Fin 3 → ℂ))
      = fun p => trivialBlockChart p.1 p.2 := eulerLocalHomeo_coe
  funext i
  cases i with
  | inl k =>
      rw [hprod, lixEtaLin_inl]
      show eulerLocalHomeo q.1 k
        = ((1 - lixTau q : ℝ) : ℂ) * (Sum.elim (aVec (lixBaseChartFun dd q).2)
              (0 : HIdx dd → ℂ) (Sum.inl k))
          + ((lixTau q : ℝ) : ℂ) * (Sum.elim (bVec (lixBaseChartFun dd q).2)
              (0 : HIdx dd → ℂ) (Sum.inl k))
          + ((lixChi (lixTau q) : ℝ) : ℂ) * (Sum.elim (0 : Fin 3 → ℂ)
              (cVec (lixBaseChartFun dd q).2) (Sum.inl k))
      rw [Sum.elim_inl, Sum.elim_inl, Sum.elim_inl, heu, lixTau_eq hu]
      show trivialBlockChart q.1.1 q.1.2 k
        = ((1 - (1 + q.1.2) / 2 : ℝ) : ℂ) * eThree k
          + (((1 + q.1.2) / 2 : ℝ) : ℂ) * (sphereChartFun q.1.1 : Fin 3 → ℂ) k
          + ((lixChi ((1 + q.1.2) / 2) : ℝ) : ℂ) * (0 : Fin 3 → ℂ) k
      rw [show (sphereChartFun q.1.1 : Fin 3 → ℂ) = sphereChartVec q.1.1 by
        show sphereChartVec (sphereClamp q.1.1) = _
        rw [sphereClamp_eq_self hsq]]
      show ((1 - (1 + q.1.2) / 2 : ℝ) : ℂ) * eThree k
          + (((1 + q.1.2) / 2 : ℝ) : ℂ) * sphereChartVec q.1.1 k = _
      simp
  | inr h =>
      rw [hprod, lixEtaLin_inr]
      show ((lixChi (lixTau q) : ℝ) : ℂ) * (cpLocalHomeo dd q.2) h.1.1 h.1.2
            * CPn.chartVec (q.2 h.1.1) h.2
        = ((1 - lixTau q : ℝ) : ℂ) * (Sum.elim (aVec (lixBaseChartFun dd q).2)
              (0 : HIdx dd → ℂ) (Sum.inr h))
          + ((lixTau q : ℝ) : ℂ) * (Sum.elim (bVec (lixBaseChartFun dd q).2)
              (0 : HIdx dd → ℂ) (Sum.inr h))
          + ((lixChi (lixTau q) : ℝ) : ℂ) * (Sum.elim (0 : Fin 3 → ℂ)
              (cVec (lixBaseChartFun dd q).2) (Sum.inr h))
      rw [Sum.elim_inr, Sum.elim_inr, Sum.elim_inr, hcp]
      show ((lixChi (lixTau q) : ℝ) : ℂ) * cpChartSection (q.2 h.1.1) h.1.2
            * CPn.chartVec (q.2 h.1.1) h.2
        = ((1 - lixTau q : ℝ) : ℂ) * (0 : HIdx dd → ℂ) h
          + ((lixTau q : ℝ) : ℂ) * (0 : HIdx dd → ℂ) h
          + ((lixChi (lixTau q) : ℝ) : ℂ) * cVec (lixBaseChartFun dd q).2 h
      rw [cVec_apply]
      show ((lixChi (lixTau q) : ℝ) : ℂ) * cpChartSection (q.2 h.1.1) h.1.2
            * CPn.chartVec (q.2 h.1.1) h.2
        = _ + _ + ((lixChi (lixTau q) : ℝ) : ℂ)
            * CPn.entry (CPn.chartAt (q.2 h.1.1)) h.2 h.1.2.succ
      rw [chartAt_entry_succ_eq]
      simp
      ring

/-! ## 5. What the reconstruction is good for -/

variable {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- **The section on the ball, in reconstructed form.**  The circle coordinate is strictly
below the equator there, so the section takes its southern branch. -/
theorem lixSection_eq_mulVec {q : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)}
    (hu : q.1.2 ∈ Ioo (-1 : ℝ) 1) (hsq : sphereQ q.1.1 ≤ 1) :
    lixSection G (lixBaseChartFun dd q)
      = mappingTorus Vmat G circHoriz circHeight (lixBaseChartFun dd q)
          *ᵥ Sum.elim 0 (lixEtaLin q (lixProductChart dd q)) := by
  have hneg : ¬ (0 : ℝ) ≤ circHeight (lixBaseChartFun dd q).1 := by
    have := circHeight_circChartFun_neg hu
    show ¬ (0 : ℝ) ≤ circHeight (circChartFun q.1.2)
    linarith
  rw [lixSection, mtSection, if_neg hneg, lixEtaLin_eq_blockSouth hu hsq]

/-- **The reconstruction lands in the fibre of `V`.**  The trivial block is untouched by
`V = 1³ ⊕ H`, and the transverse block is a scalar multiple of the base point's own lift,
which the rank-one projection fixes. -/
theorem Vmat_mulVec_lixEtaLin (q : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
    (ab : (Fin 3 → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) :
    Vmat (lixBaseChartFun dd q).2 *ᵥ lixEtaLin q ab = lixEtaLin q ab := by
  funext i
  cases i with
  | inl k =>
      show (Matrix.fromBlocks 1 0 0 (Hmat (lixBaseChartFun dd q).2)
        *ᵥ Sum.elim (fun k => lixEtaLin q ab (Sum.inl k))
            (fun h => lixEtaLin q ab (Sum.inr h))) (Sum.inl k) = _
      rw [Matrix.fromBlocks_mulVec]
      show (1 *ᵥ fun k => lixEtaLin q ab (Sum.inl k)) k
          + (0 *ᵥ fun h => lixEtaLin q ab (Sum.inr h)) k = _
      rw [Matrix.one_mulVec, Matrix.zero_mulVec]
      simp
  | inr h =>
      show (Matrix.fromBlocks 1 0 0 (Hmat (lixBaseChartFun dd q).2)
        *ᵥ Sum.elim (fun k => lixEtaLin q ab (Sum.inl k))
            (fun h => lixEtaLin q ab (Sum.inr h))) (Sum.inr h) = _
      rw [Matrix.fromBlocks_mulVec]
      show (0 *ᵥ fun k => lixEtaLin q ab (Sum.inl k)) h
          + (Hmat (lixBaseChartFun dd q).2 *ᵥ fun h => lixEtaLin q ab (Sum.inr h)) h = _
      rw [Matrix.zero_mulVec, Hmat, blockDiagonal'_mulVec]
      show (0 : HIdx dd → ℂ) h
          + ∑ k', CPn.entry (CPn.chartAt (q.2 h.1.1)) h.2 k'
              * (((lixChi (lixTau q) : ℝ) : ℂ) * ab.2 h.1.1 h.1.2
                * CPn.chartVec (q.2 h.1.1) k') = _
      have hcol : ∀ k' : Fin (dd h.1.1 + 1),
          CPn.entry (CPn.chartAt (q.2 h.1.1)) h.2 k'
              * (((lixChi (lixTau q) : ℝ) : ℂ) * ab.2 h.1.1 h.1.2
                * CPn.chartVec (q.2 h.1.1) k')
            = (((lixChi (lixTau q) : ℝ) : ℂ) * ab.2 h.1.1 h.1.2)
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
      rw [zero_add, lixEtaLin_inr]

/-- **The reconstruction is injective.**  The trivial block is read off directly, and the
transverse block at the `0`-th entry of each fibre is the chart coordinate times the
positive weight, since `chartVec` starts with a `1`. -/
theorem lixEtaLin_eq_zero_iff {q : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)}
    (hu : q.1.2 ∈ Ioo (-1 : ℝ) 1)
    (ab : (Fin 3 → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) :
    lixEtaLin q ab = 0 ↔ ab = 0 := by
  constructor
  · intro h
    have hchi : ((lixChi (lixTau q) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (lixChi_lixTau_pos hu).ne'
    refine Prod.ext ?_ ?_
    · funext k
      have := congrFun h (Sum.inl k)
      rw [lixEtaLin_inl] at this
      simpa using this
    · funext j i
      have := congrFun h (Sum.inr ⟨⟨j, i⟩, 0⟩)
      rw [lixEtaLin_inr] at this
      simp only [chartVec_zero_eq_one, mul_one] at this
      have h2 : ab.2 j i = 0 := by
        rcases mul_eq_zero.mp this with h3 | h3
        · exact absurd h3 hchi
        · exact h3
      simpa using h2
  · intro h
    subst h
    funext i
    cases i with
    | inl k => simp [lixEtaLin_inl]
    | inr h => simp [lixEtaLin_inr]

/-! Audited on every build: `#audit_axioms` prints the closure **and fails the
build** if it leaves the classical allowlist, which `#print axioms` does not. -/

#audit_axioms lixSection_eq_mulVec

end GroupApproximation.CharClass
