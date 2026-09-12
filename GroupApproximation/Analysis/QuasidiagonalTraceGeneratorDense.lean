import GroupApproximation.Analysis.AmenableTraceGeneratorDense
import GroupApproximation.Analysis.QuasidiagonalTrace

/-!
# Quasidiagonal trace models from a dense set of generators

`Analysis.AmenableTraceGeneratorDense` propagates *Hilbert--Schmidt*
multiplicativity from a spanning set to the whole algebra, which is what an
amenable trace model asks for.  A quasidiagonal trace model asks for the same
propagation in **operator** norm, and this file supplies it.

Both steps of the argument are the same as there, and the second one is
literally the same lemma:

* bilinearity of the defect `D(a,b) = φ(ab) - φ(a)φ(b)` carries operator-norm
  nullity from a set to its complex span;
* `Quasidiagonal.norm_denseGeneratorDefect_sub_le`, already stated in operator
  norm, carries it from the span to its closure.

The Hilbert--Schmidt version needs an extra conversion between the two norms
in the second step; the operator-norm version does not, so this file is
shorter than its model.

`non_mf_groups_exist.tex` uses it for the first clause of Proposition
`prop:locally-rf-by-z-trace`: there the compressions are *exactly*
multiplicative on every pair of canonical unitaries once the stage is late
enough, so the operator-norm defect is eventually zero and no Hilbert--Schmidt
estimate is available or needed.
-/

namespace GroupApproximation
namespace AmenableExtensionTrace

open Filter Matrix Quasidiagonal TracialUltraproduct
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]
variable {X : ℕ → FiniteModel}

/-! ### From a set to its span -/

/-- Operator-norm multiplicative nullity is carried to the complex span in
both variables, by bilinearity of the defect. -/
theorem tendsto_opNorm_defect_of_span
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ) (S : Set A)
    (hgen : ∀ a ∈ S, ∀ b ∈ S,
      Tendsto (fun n ↦ ‖φ n (a * b) - φ n a * φ n b‖) atTop (nhds 0)) :
    ∀ a ∈ Submodule.span ℂ S, ∀ b ∈ Submodule.span ℂ S,
      Tendsto (fun n ↦ ‖φ n (a * b) - φ n a * φ n b‖) atTop (nhds 0) := by
  have hzero : ∀ (c : A) (n : ℕ),
      ‖φ n ((0 : A) * c) - φ n 0 * φ n c‖ = 0 := by
    intro c n
    simp
  have hzero' : ∀ (c : A) (n : ℕ),
      ‖φ n (c * (0 : A)) - φ n c * φ n 0‖ = 0 := by
    intro c n
    simp
  have haddL : ∀ (a b c : A) (n : ℕ),
      φ n ((a + b) * c) - φ n (a + b) * φ n c =
        (φ n (a * c) - φ n a * φ n c) + (φ n (b * c) - φ n b * φ n c) := by
    intro a b c n
    rw [add_mul, map_add, map_add]
    noncomm_ring
  have haddR : ∀ (a b c : A) (n : ℕ),
      φ n (a * (b + c)) - φ n a * φ n (b + c) =
        (φ n (a * b) - φ n a * φ n b) + (φ n (a * c) - φ n a * φ n c) := by
    intro a b c n
    rw [mul_add, map_add, map_add]
    noncomm_ring
  have hsmulL : ∀ (z : ℂ) (a c : A) (n : ℕ),
      φ n ((z • a) * c) - φ n (z • a) * φ n c =
        z • (φ n (a * c) - φ n a * φ n c) := by
    intro z a c n
    rw [smul_mul_assoc, map_smul, map_smul, smul_mul_assoc, smul_sub]
  have hsmulR : ∀ (z : ℂ) (a c : A) (n : ℕ),
      φ n (a * (z • c)) - φ n a * φ n (z • c) =
        z • (φ n (a * c) - φ n a * φ n c) := by
    intro z a c n
    rw [mul_smul_comm, map_smul, map_smul, mul_smul_comm, smul_sub]
  have hadd : ∀ {f g : ℕ → ℝ} {h : ℕ → ℝ},
      (∀ n, 0 ≤ h n) → (∀ n, h n ≤ f n + g n) →
      Tendsto f atTop (nhds 0) → Tendsto g atTop (nhds 0) →
      Tendsto h atTop (nhds 0) := by
    intro f g h hpos hle hf hg
    exact squeeze_zero hpos hle (by simpa using hf.add hg)
  have hsmul : ∀ {f h : ℕ → ℝ} (r : ℝ),
      (∀ n, 0 ≤ h n) → (∀ n, h n ≤ r * f n) →
      Tendsto f atTop (nhds 0) → Tendsto h atTop (nhds 0) := by
    intro f h r hpos hle hf
    exact squeeze_zero hpos hle (by simpa using hf.const_mul r)
  intro a ha
  induction ha using Submodule.span_induction with
  | mem a haS =>
      intro b hb
      induction hb using Submodule.span_induction with
      | mem b hbS => exact hgen a haS b hbS
      | zero =>
          simp only [hzero' a]
          exact tendsto_const_nhds
      | add b c _ _ hb hc =>
          refine hadd (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hb hc
          rw [haddR a b c n]
          exact norm_add_le _ _
      | smul z b _ hb =>
          refine hsmul ‖z‖ (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hb
          rw [hsmulR z a b n]
          exact norm_smul_le z _
  | zero =>
      intro b _
      simp only [hzero b]
      exact tendsto_const_nhds
  | add a c _ _ ha hc =>
      intro b hb
      refine hadd (fun n ↦ norm_nonneg _) (fun n ↦ ?_) (ha b hb) (hc b hb)
      rw [haddL a c b n]
      exact norm_add_le _ _
  | smul z a _ ha =>
      intro b hb
      refine hsmul ‖z‖ (fun n ↦ norm_nonneg _) (fun n ↦ ?_) (ha b hb)
      rw [hsmulL z a b n]
      exact norm_smul_le z _

/-! ### From the span to the whole algebra -/

/-- Operator-norm multiplicativity on a dense spanning set extends to all
pairs.  Compare `Quasidiagonal.tendsto_mul_hs_of_dense_generators`, which is
the same statement in Hilbert--Schmidt norm. -/
theorem tendsto_mul_op_of_dense_generators
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hcontr : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (S : Set A)
    (hS : Dense (Submodule.span ℂ S : Set A))
    (hgen : ∀ a ∈ S, ∀ b ∈ S,
      Tendsto (fun n ↦ ‖φ n (a * b) - φ n a * φ n b‖) atTop (nhds 0)) :
    ∀ a b : A, Tendsto (fun n ↦ ‖φ n (a * b) - φ n a * φ n b‖) atTop (nhds 0) := by
  have hspan := tendsto_opNorm_defect_of_span φ S hgen
  intro a b
  refine tendsto_zero_of_forall_eventually_lt (fun n ↦ norm_nonneg _) ?_
  intro ε hε
  obtain ⟨δ, hδ0, _, hδ⟩ := exists_small_scale
    (2 * ‖a‖ + 2 * ‖b‖ + 3) (ε / 2) (by positivity) (by positivity)
  obtain ⟨p, hp, hap⟩ := Metric.mem_closure_iff.mp (hS a) δ hδ0
  obtain ⟨q, hq, hbq⟩ := Metric.mem_closure_iff.mp (hS b) δ hδ0
  have hap' : ‖a - p‖ < δ := by rwa [← dist_eq_norm]
  have hbq' : ‖b - q‖ < δ := by rwa [← dist_eq_norm]
  have hqnorm : ‖q‖ ≤ ‖b‖ + 1 := by
    have hqb : ‖q - b‖ ≤ δ := by rw [norm_sub_rev]; exact hbq'.le
    exact (norm_le_of_norm_sub_le hqb).trans (by linarith)
  have hev := eventually_lt_of_tendsto_zero (hspan p hp q hq)
    (by positivity : 0 < ε / 2)
  filter_upwards [hev] with n hn
  have hprod : ‖a * b - p * q‖ ≤ ‖a‖ * δ + δ * (‖b‖ + 1) := by
    refine (norm_mul_sub_mul_le a b p q).trans ?_
    exact add_le_add
      (mul_le_mul_of_nonneg_left hbq'.le (norm_nonneg a))
      (mul_le_mul hap'.le hqnorm (norm_nonneg _) hδ0.le)
  have herr : ‖(φ n (a * b) - φ n a * φ n b) -
      (φ n (p * q) - φ n p * φ n q)‖ ≤ ε / 2 := by
    refine (norm_denseGeneratorDefect_sub_le φ hcontr n a b p q).trans ?_
    have hraw : ‖a * b - p * q‖ + (‖a‖ * ‖b - q‖ + ‖a - p‖ * ‖q‖) ≤
        (2 * ‖a‖ + 2 * ‖b‖ + 3) * δ := by
      calc
        _ ≤ (‖a‖ * δ + δ * (‖b‖ + 1)) + (‖a‖ * δ + δ * (‖b‖ + 1)) :=
            add_le_add hprod (add_le_add
              (mul_le_mul_of_nonneg_left hbq'.le (norm_nonneg a))
              (mul_le_mul hap'.le hqnorm (norm_nonneg _) hδ0.le))
        _ ≤ (2 * ‖a‖ + 2 * ‖b‖ + 3) * δ := by nlinarith
    exact hraw.trans hδ
  have htri : ‖φ n (a * b) - φ n a * φ n b‖ ≤
      ‖(φ n (a * b) - φ n a * φ n b) - (φ n (p * q) - φ n p * φ n q)‖ +
        ‖φ n (p * q) - φ n p * φ n q‖ := by
    have h := norm_add_le
      ((φ n (a * b) - φ n a * φ n b) - (φ n (p * q) - φ n p * φ n q))
      (φ n (p * q) - φ n p * φ n q)
    simpa using h
  linarith

/-- The complete dense-generator upgrade to a quasidiagonal trace model. -/
def quasidiagonalTraceModel_of_dense_generators
    (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hone : ∀ n, φ n 1 = 1)
    (hcp : ∀ n, IsCompletelyPositiveOnMatrices (X n) ⇑(φ n))
    (hcontr : ∀ n a, ‖φ n a‖ ≤ ‖a‖) (τ : A →L[ℂ] ℂ) (S : Set A)
    (hS : Dense (Submodule.span ℂ S : Set A))
    (hmul : ∀ a ∈ S, ∀ b ∈ S,
      Tendsto (fun n ↦ ‖φ n (a * b) - φ n a * φ n b‖) atTop (nhds 0))
    (htrace : ∀ a ∈ S, Tendsto (fun n ↦
      ‖τ a - normTrace (X n) (φ n a)‖) atTop (nhds 0)) :
    QuasidiagonalTraceModel (fun a ↦ τ a) where
  space := X
  map := φ
  map_one := hone
  completelyPositive := hcp
  tendsto_mul := tendsto_mul_op_of_dense_generators φ hcontr S hS hmul
  tendsto_trace :=
    Quasidiagonal.tendsto_trace_of_dense_generators φ hcontr τ S hS htrace

end

end AmenableExtensionTrace
end GroupApproximation
