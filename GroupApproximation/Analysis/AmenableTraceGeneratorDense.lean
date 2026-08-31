import GroupApproximation.Analysis.QuasidiagonalTraceLocal
import GroupApproximation.Analysis.SoficHyperlinearTrace
import GroupApproximation.Analysis.TikuisisWhiteWinterCore

/-!
# Amenable trace models from a dense set of generators

This file isolates the analytic closure step used by group-compression
constructions.  A uniformly contractive sequence of unital completely
positive linear maps need only be checked on a set whose complex span is
dense: Hilbert--Schmidt multiplicativity is propagated first by bilinearity
to the span and then by contractivity to its closure, while the trace clause
is propagated by linearity and continuity.
-/

namespace GroupApproximation
namespace Quasidiagonal

open Filter Matrix TracialUltraproduct
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- A uniformly contractive family of linear maps, regarded as one linear map
into the bounded matrix product. -/
def boundedSequenceLinearMap
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hcontr : ∀ n a, ‖φ n a‖ ≤ ‖a‖) :
    A →ₗ[ℂ] ModelBoundedSequence X where
  toFun a := ShulmanTrace.boundedSeqOfBound (fun n ↦ φ n a) (fun n ↦ hcontr n a)
  map_add' a b := by
    apply lp.ext
    funext n
    exact map_add (φ n) a b
  map_smul' c a := by
    apply lp.ext
    funext n
    exact map_smul (φ n) c a

@[simp] theorem boundedSequenceLinearMap_apply
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hcontr : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (a : A) (n : ℕ) :
    boundedSequenceLinearMap φ hcontr a n = φ n a :=
  rfl

/-- The multiplicative defect as a bounded matrix sequence. -/
def denseGeneratorDefect
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hcontr : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (a b : A) :
    ModelBoundedSequence X :=
  boundedSequenceLinearMap φ hcontr (a * b) -
    boundedSequenceLinearMap φ hcontr a * boundedSequenceLinearMap φ hcontr b

@[simp] theorem denseGeneratorDefect_apply
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hcontr : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (a b : A) (n : ℕ) :
    denseGeneratorDefect φ hcontr a b n =
      φ n (a * b) - φ n a * φ n b :=
  rfl

theorem denseGeneratorDefect_add_left
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hcontr : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (a b c : A) :
    denseGeneratorDefect φ hcontr (a + b) c =
      denseGeneratorDefect φ hcontr a c + denseGeneratorDefect φ hcontr b c := by
  simp only [denseGeneratorDefect, add_mul, map_add]
  noncomm_ring

theorem denseGeneratorDefect_add_right
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hcontr : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (a b c : A) :
    denseGeneratorDefect φ hcontr a (b + c) =
      denseGeneratorDefect φ hcontr a b + denseGeneratorDefect φ hcontr a c := by
  simp only [denseGeneratorDefect, mul_add, map_add]
  noncomm_ring

theorem denseGeneratorDefect_smul_left
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hcontr : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (z : ℂ) (a b : A) :
    denseGeneratorDefect φ hcontr (z • a) b =
      z • denseGeneratorDefect φ hcontr a b := by
  simp only [denseGeneratorDefect, smul_mul_assoc, map_smul, smul_sub]

theorem denseGeneratorDefect_smul_right
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hcontr : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (z : ℂ) (a b : A) :
    denseGeneratorDefect φ hcontr a (z • b) =
      z • denseGeneratorDefect φ hcontr a b := by
  simp only [denseGeneratorDefect, mul_smul_comm, map_smul, smul_sub]

theorem isHilbertSchmidtNull_smul_complex
    (z : ℂ) {p : ModelBoundedSequence X}
    (hp : IsHilbertSchmidtNull X atTop p) :
    IsHilbertSchmidtNull X atTop (z • p) := by
  rw [isHilbertSchmidtNull_iff_sq] at hp ⊢
  have hc : Tendsto (fun _ : ℕ ↦ Complex.normSq z) atTop
      (nhds (Complex.normSq z)) := tendsto_const_nhds
  have h := hc.mul hp
  simpa only [ShulmanTrace.modelSeq_smul_apply, hsNormSq_smul, mul_zero] using h

/-- Generator-pair Hilbert--Schmidt convergence extends to the complex span
in both variables. -/
theorem isHilbertSchmidtNull_denseGeneratorDefect_of_span
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hcontr : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (S : Set A)
    (hgen : ∀ a ∈ S, ∀ b ∈ S,
      IsHilbertSchmidtNull X atTop (denseGeneratorDefect φ hcontr a b)) :
    ∀ a ∈ Submodule.span ℂ S, ∀ b ∈ Submodule.span ℂ S,
      IsHilbertSchmidtNull X atTop (denseGeneratorDefect φ hcontr a b) := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem a haS =>
      intro b hb
      induction hb using Submodule.span_induction with
      | mem b hbS => exact hgen a haS b hbS
      | zero => simpa [denseGeneratorDefect] using IsHilbertSchmidtNull.zero X atTop
      | add b c _ _ hb hc =>
          rw [denseGeneratorDefect_add_right]
          exact IsHilbertSchmidtNull.add X atTop hb hc
      | smul z b _ hb =>
          rw [denseGeneratorDefect_smul_right]
          exact isHilbertSchmidtNull_smul_complex z hb
  | zero =>
      intro b hb
      simpa [denseGeneratorDefect] using IsHilbertSchmidtNull.zero X atTop
  | add a c _ _ ha hc =>
      intro b hb
      rw [denseGeneratorDefect_add_left]
      exact IsHilbertSchmidtNull.add X atTop (ha b hb) (hc b hb)
  | smul z a _ ha =>
      intro b hb
      rw [denseGeneratorDefect_smul_left]
      exact isHilbertSchmidtNull_smul_complex z (ha b hb)

omit [∀ n, Nonempty (X n)] in
/-- The operator-norm distance between two multiplicative defects is uniformly
controlled by the distances between their inputs. -/
theorem norm_denseGeneratorDefect_sub_le
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hcontr : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (n : ℕ) (a b p q : A) :
    ‖(φ n (a * b) - φ n a * φ n b) -
        (φ n (p * q) - φ n p * φ n q)‖ ≤
      ‖a * b - p * q‖ +
        (‖a‖ * ‖b - q‖ + ‖a - p‖ * ‖q‖) := by
  have hfirst : ‖φ n (a * b) - φ n (p * q)‖ ≤ ‖a * b - p * q‖ := by
    rw [← map_sub]
    exact hcontr n _
  have hsecond : ‖φ n a * φ n b - φ n p * φ n q‖ ≤
      ‖a‖ * ‖b - q‖ + ‖a - p‖ * ‖q‖ := by
    have hsplit : φ n a * φ n b - φ n p * φ n q =
        φ n a * (φ n b - φ n q) + (φ n a - φ n p) * φ n q := by
      noncomm_ring
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (Matrix.l2_opNorm_mul _ _).trans ?_
      refine mul_le_mul (hcontr n a) ?_ (norm_nonneg _) (norm_nonneg _)
      rw [← map_sub]
      exact hcontr n _
    · refine (Matrix.l2_opNorm_mul _ _).trans ?_
      refine mul_le_mul ?_ (hcontr n q) (norm_nonneg _) (norm_nonneg _)
      rw [← map_sub]
      exact hcontr n _
  have hsplit :
      (φ n (a * b) - φ n a * φ n b) -
          (φ n (p * q) - φ n p * φ n q) =
        (φ n (a * b) - φ n (p * q)) -
          (φ n a * φ n b - φ n p * φ n q) := by abel
  rw [hsplit]
  exact (norm_sub_le _ _).trans (add_le_add hfirst hsecond)

/-- Hilbert--Schmidt multiplicativity on a dense spanning set extends to all
pairs. -/
theorem tendsto_mul_hs_of_dense_generators
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hcontr : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (S : Set A)
    (hS : Dense (Submodule.span ℂ S : Set A))
    (hgen : ∀ a ∈ S, ∀ b ∈ S,
      Tendsto (fun n ↦ hsNorm (X n)
        (φ n (a * b) - φ n a * φ n b)) atTop (nhds 0)) :
    ∀ a b : A, Tendsto (fun n ↦ hsNorm (X n)
      (φ n (a * b) - φ n a * φ n b)) atTop (nhds 0) := by
  have hspan := isHilbertSchmidtNull_denseGeneratorDefect_of_span φ hcontr S
    (fun a ha b hb ↦ hgen a ha b hb)
  intro a b
  refine tendsto_zero_of_forall_eventually_lt (fun n ↦ hsNorm_nonneg _ _) ?_
  intro ε hε
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := exists_small_scale
    (2 * ‖a‖ + 2 * ‖b‖ + 3) (ε / 4) (by positivity) (by positivity)
  obtain ⟨p, hp, hap⟩ := Metric.mem_closure_iff.mp (hS a) δ hδ0
  obtain ⟨q, hq, hbq⟩ := Metric.mem_closure_iff.mp (hS b) δ hδ0
  have hap' : ‖a - p‖ < δ := by rwa [← dist_eq_norm]
  have hbq' : ‖b - q‖ < δ := by rwa [← dist_eq_norm]
  have hqnorm : ‖q‖ ≤ ‖b‖ + 1 := by
    have hqb : ‖q - b‖ ≤ δ := by rw [norm_sub_rev]; exact hbq'.le
    exact (norm_le_of_norm_sub_le hqb).trans (by linarith)
  have hbase := (isHilbertSchmidtNull_iff_sq X atTop
    (denseGeneratorDefect φ hcontr p q)).mp (hspan p hp q hq)
  have hev := eventually_lt_of_tendsto_zero hbase (by positivity : 0 < ε ^ 2 / 4)
  filter_upwards [hev] with n hn
  let Da := φ n (a * b) - φ n a * φ n b
  let Dp := φ n (p * q) - φ n p * φ n q
  have hprod : ‖a * b - p * q‖ ≤ ‖a‖ * δ + δ * (‖b‖ + 1) := by
    refine (norm_mul_sub_mul_le a b p q).trans ?_
    exact add_le_add
      (mul_le_mul_of_nonneg_left hbq'.le (norm_nonneg a))
      (mul_le_mul hap'.le hqnorm (norm_nonneg _) hδ0.le)
  have herr : ‖Da - Dp‖ ≤ ε / 4 := by
    refine (norm_denseGeneratorDefect_sub_le φ hcontr n a b p q).trans ?_
    have hraw : ‖a * b - p * q‖ +
        (‖a‖ * ‖b - q‖ + ‖a - p‖ * ‖q‖) ≤
        (2 * ‖a‖ + 2 * ‖b‖ + 3) * δ := by
      calc
        _ ≤ (‖a‖ * δ + δ * (‖b‖ + 1)) +
            (‖a‖ * δ + δ * (‖b‖ + 1)) := by
              exact add_le_add hprod (add_le_add
                (mul_le_mul_of_nonneg_left hbq'.le (norm_nonneg a))
                (mul_le_mul hap'.le hqnorm (norm_nonneg _) hδ0.le))
        _ ≤ (2 * ‖a‖ + 2 * ‖b‖ + 3) * δ := by nlinarith
    exact hraw.trans hδ
  have herrhs : hsNormSq (X n) (Da - Dp) ≤ (ε / 4) ^ 2 :=
    (PrelimNotation.hsNormSq_le_sq_l2_opNorm (X n) (Da - Dp)).trans
      (pow_le_pow_left₀ (norm_nonneg _) herr 2)
  have hsum : hsNormSq (X n) Da ≤
      2 * hsNormSq (X n) Dp + 2 * hsNormSq (X n) (Da - Dp) := by
    have h := hsNormSq_add_le (X n) Dp (Da - Dp)
    have heq : Dp + (Da - Dp) = Da := by abel
    rwa [heq] at h
  have hsq : hsNormSq (X n) Da < ε ^ 2 := by
    have hDp : hsNormSq (X n) Dp < ε ^ 2 / 4 := by simpa [Dp] using hn
    nlinarith [hsum, herrhs, sq_nonneg ε]
  have hsquare : hsNorm (X n) Da ^ 2 = hsNormSq (X n) Da := sq_hsNorm _ _
  have hnonneg := hsNorm_nonneg (X n) Da
  change hsNorm (X n) Da < ε
  nlinarith

omit [∀ n, Nonempty (X n)] in
/-- Trace convergence on generators extends to the whole algebra. -/
theorem tendsto_trace_of_dense_generators
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hcontr : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (τ : A →L[ℂ] ℂ) (S : Set A)
    (hS : Dense (Submodule.span ℂ S : Set A))
    (hgen : ∀ a ∈ S, Tendsto (fun n ↦
      ‖τ a - normTrace (X n) (φ n a)‖) atTop (nhds 0)) :
    ∀ a : A, Tendsto (fun n ↦
      ‖τ a - normTrace (X n) (φ n a)‖) atTop (nhds 0) := by
  have hspan : ∀ a ∈ Submodule.span ℂ S,
      Tendsto (fun n ↦ τ a - normTrace (X n) (φ n a)) atTop (nhds 0) := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a haS =>
        rw [tendsto_zero_iff_norm_tendsto_zero]
        exact hgen a haS
    | zero =>
        refine tendsto_const_nhds.congr fun n ↦ ?_
        rw [map_zero, map_zero, normTrace_zero, sub_zero]
    | add a b _ _ ha hb =>
        have h0 : Tendsto (fun n ↦
            (τ a - normTrace (X n) (φ n a)) +
              (τ b - normTrace (X n) (φ n b))) atTop (nhds 0) := by
          simpa using ha.add hb
        refine h0.congr fun n ↦ ?_
        rw [map_add, map_add, normTrace_add]
        ring
    | smul z a _ ha =>
        have h0 : Tendsto (fun n ↦
            z * (τ a - normTrace (X n) (φ n a))) atTop (nhds 0) := by
          simpa using ha.const_mul z
        refine h0.congr fun n ↦ ?_
        rw [map_smul, map_smul, normTrace_smul, smul_eq_mul]
        ring
  intro a
  refine tendsto_zero_of_forall_eventually_lt (fun n ↦ norm_nonneg _) ?_
  intro ε hε
  obtain ⟨δ, hδ0, _, hδ⟩ := exists_small_scale (‖τ‖ + 1) (ε / 2)
    (by positivity) (by positivity)
  obtain ⟨p, hp, hap⟩ := Metric.mem_closure_iff.mp (hS a) δ hδ0
  have hap' : ‖a - p‖ < δ := by rwa [← dist_eq_norm]
  have hpnorm : Tendsto (fun n ↦
      ‖τ p - normTrace (X n) (φ n p)‖) atTop (nhds 0) := by
    simpa using (hspan p hp).norm
  have hev := eventually_lt_of_tendsto_zero hpnorm (by positivity : 0 < ε / 2)
  filter_upwards [hev] with n hn
  have hτ : ‖τ a - τ p‖ ≤ ‖τ‖ * ‖a - p‖ := by
    rw [← map_sub]
    exact τ.le_opNorm _
  have hmodel : ‖normTrace (X n) (φ n p) - normTrace (X n) (φ n a)‖
      ≤ ‖a - p‖ := by
    rw [← normTrace_sub, ← map_sub]
    exact (PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm (X n)
      (φ n (p - a))).trans
      ((hcontr n (p - a)).trans (le_of_eq (norm_sub_rev p a)))
  have hτδ : ‖τ a - τ p‖ ≤ ‖τ‖ * δ :=
    hτ.trans (mul_le_mul_of_nonneg_left hap'.le (norm_nonneg τ))
  have hmodelδ :
      ‖normTrace (X n) (φ n p) - normTrace (X n) (φ n a)‖ < δ :=
    hmodel.trans_lt hap'
  have hsplit : τ a - normTrace (X n) (φ n a) =
      (τ a - τ p) + (τ p - normTrace (X n) (φ n p)) +
        (normTrace (X n) (φ n p) - normTrace (X n) (φ n a)) := by ring
  rw [hsplit]
  calc
    _ ≤ ‖τ a - τ p‖ + ‖τ p - normTrace (X n) (φ n p)‖ +
        ‖normTrace (X n) (φ n p) - normTrace (X n) (φ n a)‖ := by
          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ < (‖τ‖ + 1) * δ + ε / 2 := by
      nlinarith [hτδ, hmodelδ, hn]
    _ ≤ ε := by linarith

/-- The complete dense-generator upgrade to an amenable trace model. -/
def amenableTraceModel_of_dense_generators
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hone : ∀ n, φ n 1 = 1)
    (hcp : ∀ n, IsCompletelyPositiveOnMatrices (X n) ⇑(φ n))
    (hcontr : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (τ : A →L[ℂ] ℂ) (S : Set A)
    (hS : Dense (Submodule.span ℂ S : Set A))
    (hmul : ∀ a ∈ S, ∀ b ∈ S, Tendsto (fun n ↦ hsNorm (X n)
      (φ n (a * b) - φ n a * φ n b)) atTop (nhds 0))
    (htrace : ∀ a ∈ S, Tendsto (fun n ↦
      ‖τ a - normTrace (X n) (φ n a)‖) atTop (nhds 0)) :
    AmenableTraceModel τ where
  space := X
  map := φ
  map_one := hone
  completelyPositive := hcp
  tendsto_mul_hs := tendsto_mul_hs_of_dense_generators φ hcontr S hS hmul
  tendsto_trace := tendsto_trace_of_dense_generators φ hcontr τ S hS htrace

end

end Quasidiagonal
end GroupApproximation
