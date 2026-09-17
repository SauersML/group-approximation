import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.BrownROmega.TwoNorm
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.NoncommRing
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown's formulation: the bounded resolvent `q(t) = t / (1 + t²)`

`simple_kazhdan_sofic_group.tex`, subsection "Brown's formulation": "`L(G)` embeds in `𝓡^ω`" and
"`L(G) ⊗̄ 𝓡` ... embeds in `𝓡^ω`".

Second step of this lane's route to those embeddings (the first is `Full/BrownROmega/TwoNorm`).
For a self-adjoint `a` of a unital C⋆-algebra, the continuous functional calculus gives
`q(a) = a (1 + a²)⁻¹`, with `R_a = (1 + a²)⁻¹`:

* `‖R_a‖ ≤ 1` and `‖q(a)‖ ≤ 1/2`, and `q(a)` lies in every von Neumann algebra containing `a`
  (bicommutant and `Commute.cfc_real`);
* `q(a) − q(b) = R_a (a − b) R_b − R_a a (a − b) (b R_b)`, so for a tracial vector `ξ`,
  `‖(q(a) − q(b)) ξ‖ ≤ 2 ‖(a − b) ξ‖` (both `R_a a` and `b R_b` are `q`, of norm `≤ 1/2`);
* `q(g(T)) = T` for `g(s) = 2s / (1 + √(1 − 4s²))` and `‖T‖ ≤ 1/2`;
* `q` is uniformly approximated on `{‖a‖ ≤ R}` by fixed complex polynomials (Weierstrass).

The later files use these facts where a proof would otherwise need Kaplansky's density theorem.
-/

namespace GroupApproximation.Full.SK06

open Filter TracialUltrapower Polynomial
open scoped InnerProductSpace Topology

noncomputable section

/-! ### The scalar functions -/

/-- `r(t) = (1 + t²)⁻¹`. -/
def rfun (t : ℝ) : ℝ := (1 + t ^ 2)⁻¹

/-- `q(t) = t (1 + t²)⁻¹`. -/
def qfun (t : ℝ) : ℝ := t * (1 + t ^ 2)⁻¹

/-- `g(s) = 2s (1 + √(1 − 4s²))⁻¹`, the inverse of `q` on `[-1/2, 1/2]`. -/
def gfun (s : ℝ) : ℝ := 2 * s * (1 + Real.sqrt (1 - 4 * s ^ 2))⁻¹

theorem continuous_rfun : Continuous rfun := by
  have h : Continuous fun t : ℝ ↦ 1 + t ^ 2 := by fun_prop
  exact h.inv₀ fun t ↦ (show (0 : ℝ) < 1 + t ^ 2 by positivity).ne'

theorem continuous_qfun : Continuous qfun := by
  show Continuous fun t : ℝ ↦ t * rfun t
  exact continuous_id.mul continuous_rfun

theorem continuous_gfun : Continuous gfun := by
  have h : Continuous fun s : ℝ ↦ 1 + Real.sqrt (1 - 4 * s ^ 2) := by fun_prop
  have h' : Continuous fun s : ℝ ↦ (1 + Real.sqrt (1 - 4 * s ^ 2))⁻¹ :=
    h.inv₀ fun s ↦ (show (0 : ℝ) < 1 + Real.sqrt (1 - 4 * s ^ 2) by positivity).ne'
  show Continuous fun s : ℝ ↦ 2 * s * (1 + Real.sqrt (1 - 4 * s ^ 2))⁻¹
  exact (continuous_const.mul continuous_id).mul h'

theorem abs_qfun_le (t : ℝ) : |qfun t| ≤ 1 / 2 := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [qfun, abs_mul, abs_of_pos (inv_pos.mpr hpos), ← div_eq_mul_inv, div_le_iff₀ hpos]
  nlinarith [sq_nonneg (|t| - 1), sq_abs t]

/-- The algebra behind `q ∘ g = id`. -/
theorem qfun_eq_of {g s u : ℝ} (hu0 : 0 ≤ u) (hu2 : u ^ 2 = 1 - 4 * s ^ 2)
    (hg : g * (1 + u) = 2 * s) : qfun g = s := by
  have h1u : (1 + u) ≠ 0 := (show (0 : ℝ) < 1 + u by linarith).ne'
  have h1g : (1 + g ^ 2) ≠ 0 := (show (0 : ℝ) < 1 + g ^ 2 by positivity).ne'
  have h4 : g ^ 2 * (1 + u) * (1 + u) = (1 - u) * (1 + u) := by
    linear_combination (g * (1 + u) + 2 * s) * hg + hu2
  have h5 : g ^ 2 * (1 + u) = 1 - u := mul_right_cancel₀ h1u h4
  have hsum : (1 + g ^ 2) * (1 + u) = 2 := by linear_combination h5
  show g * (1 + g ^ 2)⁻¹ = s
  rw [mul_inv_eq_iff_eq_mul₀ h1g]
  exact mul_right_cancel₀ h1u (by linear_combination hg - s * hsum)

theorem qfun_gfun {s : ℝ} (hs : |s| ≤ 1 / 2) : qfun (gfun s) = s := by
  have h4s : 0 ≤ 1 - 4 * s ^ 2 := by nlinarith [abs_nonneg s, sq_abs s]
  have hu0 : 0 ≤ Real.sqrt (1 - 4 * s ^ 2) := Real.sqrt_nonneg _
  have hu2 : Real.sqrt (1 - 4 * s ^ 2) ^ 2 = 1 - 4 * s ^ 2 := Real.sq_sqrt h4s
  have h1u : (1 + Real.sqrt (1 - 4 * s ^ 2)) ≠ 0 :=
    (show (0 : ℝ) < 1 + Real.sqrt (1 - 4 * s ^ 2) by positivity).ne'
  exact qfun_eq_of hu0 hu2 (inv_mul_cancel_right₀ h1u (2 * s))

/-! ### The functional calculus in a C⋆-algebra -/

section CStar

variable {A : Type*} [CStarAlgebra A]

theorem cfc_one_add_mul_self (a : A) (ha : IsSelfAdjoint a) :
    cfc (fun t : ℝ ↦ 1 + t * t) a = 1 + a * a := by
  rw [cfc_add a (fun _ : ℝ ↦ (1 : ℝ)) (fun t : ℝ ↦ t * t), cfc_const_one ℝ a ha,
    cfc_mul (fun t : ℝ ↦ t) (fun t : ℝ ↦ t) a, cfc_id' ℝ a ha]

theorem cfc_rfun_mul (a : A) (ha : IsSelfAdjoint a) : cfc rfun a * (1 + a * a) = 1 := by
  have h := cfc_mul rfun (fun t : ℝ ↦ 1 + t * t) a continuous_rfun.continuousOn
  rw [cfc_one_add_mul_self a ha] at h
  rw [← h]
  calc cfc (fun t : ℝ ↦ rfun t * (1 + t * t)) a = cfc (fun _ : ℝ ↦ (1 : ℝ)) a := by
        refine cfc_congr fun t _ ↦ ?_
        show (1 + t ^ 2)⁻¹ * (1 + t * t) = 1
        rw [← pow_two]
        exact inv_mul_cancel₀ (show (0 : ℝ) < 1 + t ^ 2 by positivity).ne'
    _ = 1 := cfc_const_one ℝ a ha

theorem cfc_mul_rfun (a : A) (ha : IsSelfAdjoint a) : (1 + a * a) * cfc rfun a = 1 := by
  have h := cfc_mul (fun t : ℝ ↦ 1 + t * t) rfun a (hg := continuous_rfun.continuousOn)
  rw [cfc_one_add_mul_self a ha] at h
  rw [← h]
  calc cfc (fun t : ℝ ↦ (1 + t * t) * rfun t) a = cfc (fun _ : ℝ ↦ (1 : ℝ)) a := by
        refine cfc_congr fun t _ ↦ ?_
        show (1 + t * t) * (1 + t ^ 2)⁻¹ = 1
        rw [← pow_two]
        exact mul_inv_cancel₀ (show (0 : ℝ) < 1 + t ^ 2 by positivity).ne'
    _ = 1 := cfc_const_one ℝ a ha

theorem cfc_qfun_eq_rfun_mul (a : A) (ha : IsSelfAdjoint a) : cfc qfun a = cfc rfun a * a := by
  have h := cfc_mul rfun (fun t : ℝ ↦ t) a continuous_rfun.continuousOn
  rw [cfc_id' ℝ a ha] at h
  rw [← h]
  refine cfc_congr fun t _ ↦ ?_
  show t * (1 + t ^ 2)⁻¹ = (1 + t ^ 2)⁻¹ * t
  exact mul_comm _ _

theorem cfc_qfun_eq_mul_rfun (a : A) (ha : IsSelfAdjoint a) : cfc qfun a = a * cfc rfun a := by
  have h := cfc_mul (fun t : ℝ ↦ t) rfun a (hg := continuous_rfun.continuousOn)
  rw [cfc_id' ℝ a ha] at h
  rw [← h]
  exact cfc_congr fun t _ ↦ rfl

theorem norm_cfc_rfun_le (a : A) : ‖cfc rfun a‖ ≤ 1 := by
  refine norm_cfc_le zero_le_one fun t _ ↦ ?_
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [Real.norm_eq_abs, rfun, abs_of_pos (inv_pos.mpr hpos)]
  exact inv_le_one_of_one_le₀ (le_add_of_nonneg_right (sq_nonneg t))

theorem norm_cfc_qfun_le (a : A) : ‖cfc qfun a‖ ≤ 1 / 2 := by
  refine norm_cfc_le (by norm_num) fun t _ ↦ ?_
  rw [Real.norm_eq_abs]
  exact abs_qfun_le t

theorem norm_rfun_mul_le (a : A) (ha : IsSelfAdjoint a) : ‖cfc rfun a * a‖ ≤ 1 / 2 := by
  rw [← cfc_qfun_eq_rfun_mul a ha]
  exact norm_cfc_qfun_le a

theorem norm_mul_rfun_le (a : A) (ha : IsSelfAdjoint a) : ‖a * cfc rfun a‖ ≤ 1 / 2 := by
  rw [← cfc_qfun_eq_mul_rfun a ha]
  exact norm_cfc_qfun_le a

/-- `q(a) − q(b) = R_a (a − b) R_b − R_a a (a − b) (b R_b)`. -/
theorem rfun_mul_sub_mul_rfun (a b : A) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    cfc rfun a * a - b * cfc rfun b =
      cfc rfun a * (a - b) * cfc rfun b - cfc rfun a * a * (a - b) * (b * cfc rfun b) := by
  calc cfc rfun a * a - b * cfc rfun b
      = cfc rfun a * a * ((1 + b * b) * cfc rfun b)
          - cfc rfun a * (1 + a * a) * b * cfc rfun b := by
        rw [cfc_mul_rfun b hb, cfc_rfun_mul a ha, mul_one, one_mul]
    _ = cfc rfun a * (a - b) * cfc rfun b - cfc rfun a * a * (a - b) * (b * cfc rfun b) := by
        noncomm_ring

/-- `q(g(T)) = T` for a self-adjoint `T` with `‖T‖ ≤ 1/2`. -/
theorem cfc_qfun_cfc_gfun (T : A) (hT : IsSelfAdjoint T) (hTn : ‖T‖ ≤ 1 / 2) :
    cfc qfun (cfc gfun T) = T := by
  obtain _ | _ := subsingleton_or_nontrivial A
  · exact Subsingleton.elim _ _
  have hcongr : (spectrum ℝ T).EqOn (fun s ↦ qfun (gfun s)) (fun s ↦ s) := by
    intro s hs
    have h := spectrum.norm_le_norm_of_mem hs
    rw [Real.norm_eq_abs] at h
    exact qfun_gfun (h.trans hTn)
  rw [← cfc_comp' qfun gfun T continuous_qfun.continuousOn continuous_gfun.continuousOn hT,
    cfc_congr hcongr, cfc_id' ℝ T hT]

end CStar

/-! ### Complex polynomials -/

section Poly

/-- `∑_{i < m} cᵢ xⁱ`. -/
def polyEval {B : Type*} [Ring B] [Algebra ℂ B] (c : ℕ → ℂ) (m : ℕ) (x : B) : B :=
  ∑ i ∈ Finset.range m, c i • x ^ i

theorem map_polyEval {B C F : Type*} [Ring B] [Algebra ℂ B] [Ring C] [Algebra ℂ C]
    [FunLike F B C] [AlgHomClass F ℂ B C] (φ : F) (c : ℕ → ℂ) (m : ℕ) (x : B) :
    φ (polyEval c m x) = polyEval c m (φ x) := by
  simp only [polyEval, map_sum, map_smul, map_pow]

theorem polyEval_mem {B S : Type*} [Ring B] [Algebra ℂ B] [SetLike S B] [SubsemiringClass S B]
    [SMulMemClass S ℂ B] {s : S} {x : B} (hx : x ∈ s) (c : ℕ → ℂ) (m : ℕ) :
    polyEval c m x ∈ s :=
  _root_.sum_mem fun i _ ↦ SMulMemClass.smul_mem (c i) (pow_mem hx i)

/-- A real polynomial `ε`-close to `q` on `[-R, R]` is `ε`-close to `q` in norm on self-adjoint
elements of norm `≤ R`. -/
theorem norm_polyEval_sub_cfc_qfun_le {A : Type*} [CStarAlgebra A] {R ε : ℝ} (hε : 0 < ε)
    (p : ℝ[X]) (hp : ∀ x ∈ Set.Icc (-R) R, |p.eval x - qfun x| < ε) (a : A)
    (ha : IsSelfAdjoint a) (haR : ‖a‖ ≤ R) :
    ‖polyEval (fun i ↦ ((p.coeff i : ℝ) : ℂ)) (p.natDegree + 1) a - cfc qfun a‖ ≤ ε := by
  obtain _ | _ := subsingleton_or_nontrivial A
  · rw [Subsingleton.elim (polyEval (fun i ↦ ((p.coeff i : ℝ) : ℂ)) (p.natDegree + 1) a
      - cfc qfun a) 0, norm_zero]
    exact hε.le
  have hpoly : polyEval (fun i ↦ ((p.coeff i : ℝ) : ℂ)) (p.natDegree + 1) a = cfc p.eval a := by
    rw [polyEval, cfc_polynomial p a ha, Polynomial.aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact Complex.coe_smul (p.coeff i) (a ^ i)
  rw [hpoly, ← cfc_sub p.eval qfun a p.continuous.continuousOn continuous_qfun.continuousOn]
  refine norm_cfc_le hε.le fun t ht ↦ ?_
  have h := spectrum.norm_le_norm_of_mem ht
  rw [Real.norm_eq_abs] at h
  rw [Real.norm_eq_abs]
  exact (hp t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩).le

/-- **Uniform polynomial approximation of `q`** on self-adjoint elements of norm `≤ R`, with the
same polynomial in two C⋆-algebras. -/
theorem exists_poly_approx {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] (R ε : ℝ)
    (hε : 0 < ε) :
    ∃ (c : ℕ → ℂ) (m : ℕ), (∀ a : A, IsSelfAdjoint a → ‖a‖ ≤ R →
      ‖polyEval c m a - cfc qfun a‖ ≤ ε) ∧ ∀ b : B, IsSelfAdjoint b → ‖b‖ ≤ R →
      ‖polyEval c m b - cfc qfun b‖ ≤ ε := by
  obtain ⟨p, hp⟩ :=
    exists_polynomial_near_of_continuousOn (-R) R qfun continuous_qfun.continuousOn ε hε
  exact ⟨fun i ↦ ((p.coeff i : ℝ) : ℂ), p.natDegree + 1, norm_polyEval_sub_cfc_qfun_le hε p hp,
    norm_polyEval_sub_cfc_qfun_le hε p hp⟩

end Poly

/-! ### Operators -/

section Operators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- The functional calculus stays in a von Neumann algebra. -/
theorem cfc_mem_of_mem {x : H →L[ℂ] H} (hx : x ∈ M) (f : ℝ → ℝ) : cfc f x ∈ M := by
  rw [← VonNeumannAlgebra.commutant_commutant M, VonNeumannAlgebra.mem_commutant_iff]
  intro g hg
  exact (Commute.cfc_real (VonNeumannAlgebra.mem_commutant_iff.mp hg x hx) f).eq.symm

/-- **`‖(q(a) − q(b)) ξ‖ ≤ 2 ‖(a − b) ξ‖`** for a tracial vector `ξ`. -/
theorem norm_qfun_sub_apply_le (τ : TracialVector M) {a b : H →L[ℂ] H} (haM : a ∈ M)
    (hbM : b ∈ M) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    ‖(cfc qfun a - cfc qfun b) τ.vec‖ ≤ 2 * ‖(a - b) τ.vec‖ := by
  have hRa : cfc rfun a ∈ M := cfc_mem_of_mem haM rfun
  have hRb : cfc rfun b ∈ M := cfc_mem_of_mem hbM rfun
  have hab : a - b ∈ M := sub_mem haM hbM
  have h1 : ‖(cfc rfun a * (a - b) * cfc rfun b) τ.vec‖ ≤ ‖(a - b) τ.vec‖ := by
    calc ‖(cfc rfun a * (a - b) * cfc rfun b) τ.vec‖
        ≤ ‖cfc rfun b‖ * ‖(cfc rfun a * (a - b)) τ.vec‖ :=
          τ.norm_mul_apply_le (mul_mem hRa hab) hRb
      _ ≤ 1 * ‖(cfc rfun a * (a - b)) τ.vec‖ :=
          mul_le_mul_of_nonneg_right (norm_cfc_rfun_le b) (norm_nonneg _)
      _ = ‖cfc rfun a ((a - b) τ.vec)‖ := one_mul _
      _ ≤ ‖cfc rfun a‖ * ‖(a - b) τ.vec‖ := (cfc rfun a).le_opNorm _
      _ ≤ 1 * ‖(a - b) τ.vec‖ :=
          mul_le_mul_of_nonneg_right (norm_cfc_rfun_le a) (norm_nonneg _)
      _ = ‖(a - b) τ.vec‖ := one_mul _
  have h2 : ‖(cfc rfun a * a * (a - b) * (b * cfc rfun b)) τ.vec‖ ≤ ‖(a - b) τ.vec‖ := by
    calc ‖(cfc rfun a * a * (a - b) * (b * cfc rfun b)) τ.vec‖
        ≤ ‖b * cfc rfun b‖ * ‖(cfc rfun a * a * (a - b)) τ.vec‖ :=
          τ.norm_mul_apply_le (mul_mem (mul_mem hRa haM) hab) (mul_mem hbM hRb)
      _ ≤ 1 * ‖(cfc rfun a * a * (a - b)) τ.vec‖ :=
          mul_le_mul_of_nonneg_right ((norm_mul_rfun_le b hb).trans (by norm_num))
            (norm_nonneg _)
      _ = ‖(cfc rfun a * a) ((a - b) τ.vec)‖ := one_mul _
      _ ≤ ‖cfc rfun a * a‖ * ‖(a - b) τ.vec‖ := (cfc rfun a * a).le_opNorm _
      _ ≤ 1 * ‖(a - b) τ.vec‖ :=
          mul_le_mul_of_nonneg_right ((norm_rfun_mul_le a ha).trans (by norm_num))
            (norm_nonneg _)
      _ = ‖(a - b) τ.vec‖ := one_mul _
  rw [cfc_qfun_eq_rfun_mul a ha, cfc_qfun_eq_mul_rfun b hb, rfun_mul_sub_mul_rfun a b ha hb,
    _root_.sub_apply]
  refine (norm_sub_le _ _).trans ?_
  linarith

end Operators

/-! ### Sequences in the ultrapower -/

section Seq

universe v

variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {N : VonNeumannAlgebra K} (σ : TracialVector N) (ω : Ultrafilter ℕ)

/-- `n ↦ q(rₙ)`, bounded by `1/2`. -/
def qseq (r : boundedSeq N) : boundedSeq N :=
  ⟨fun n ↦ cfc qfun ((r : ℕ → (K →L[ℂ] K)) n),
    mem_boundedSeq_iff.mpr ⟨fun n ↦ cfc_mem_of_mem (coord_mem r n) qfun, 1 / 2,
      fun n ↦ norm_cfc_qfun_le ((r : ℕ → (K →L[ℂ] K)) n)⟩⟩

theorem qseq_apply (r : boundedSeq N) (n : ℕ) :
    (qseq r : ℕ → (K →L[ℂ] K)) n = cfc qfun ((r : ℕ → (K →L[ℂ] K)) n) := rfl

theorem norm_qseq_le (r : boundedSeq N) (n : ℕ) : ‖(qseq r : ℕ → (K →L[ℂ] K)) n‖ ≤ 1 / 2 :=
  norm_cfc_qfun_le _

/-- `‖q(r) − q(s)‖₂ ≤ 2 ‖r − s‖₂` for sequences of self-adjoint operators. -/
theorem twoNorm_mk_qseq_sub_le {r s : boundedSeq N}
    (hr : ∀ n, IsSelfAdjoint ((r : ℕ → (K →L[ℂ] K)) n))
    (hs : ∀ n, IsSelfAdjoint ((s : ℕ → (K →L[ℂ] K)) n)) :
    twoNorm σ ω (mk σ ω (qseq r) - mk σ ω (qseq s)) ≤ 2 * twoNorm σ ω (mk σ ω r - mk σ ω s) := by
  rw [← map_sub (mk σ ω), ← map_sub (mk σ ω)]
  refine twoNorm_mk_le σ ω ((tendsto_twoNorm_mk σ ω (r - s)).const_mul 2) fun n ↦ ?_
  exact norm_qfun_sub_apply_le σ (coord_mem r n) (coord_mem s n) (hr n) (hs n)

end Seq

end

end GroupApproximation.Full.SK06

#audit_axioms GroupApproximation.Full.SK06.cfc_qfun_cfc_gfun
#audit_axioms GroupApproximation.Full.SK06.exists_poly_approx
#audit_axioms GroupApproximation.Full.SK06.norm_qfun_sub_apply_le
#audit_axioms GroupApproximation.Full.SK06.twoNorm_mk_qseq_sub_le
