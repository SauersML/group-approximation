import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import GroupApproximation.Meta.AxiomGuard

/-!
# Extending asymptotic compatibility from a dense family

Shulman's symmetric-double argument first makes two contractive asymptotic
homomorphisms agree, with improving error, on longer and longer initial
segments of a dense sequence in the amalgamated algebra.  The argument then
uses contractivity and asymptotic additivity to obtain agreement on every
element.

This file isolates that analytic completion step.  It does not assume an
amalgamated-free-product permanence theorem or a commutant-lifting theorem.
-/

namespace GroupApproximation
namespace ShulmanDenseCompatibility

open Filter

noncomputable section

universe u v

variable {C : Type u} {E : Type v}
  [NormedAddCommGroup C] [NormedAddCommGroup E]

/-- Agreement of two contractive asymptotically additive families on a dense
set extends to every source element. -/
theorem tendsto_norm_sub_of_dense
    (f g : ℕ → C → E)
    (hfadd : ∀ x y : C,
      Tendsto (fun n ↦ ‖f n (x + y) - f n x - f n y‖) atTop (nhds 0))
    (hgadd : ∀ x y : C,
      Tendsto (fun n ↦ ‖g n (x + y) - g n x - g n y‖) atTop (nhds 0))
    (hfcontract : ∀ n x, ‖f n x‖ ≤ ‖x‖)
    (hgcontract : ∀ n x, ‖g n x‖ ≤ ‖x‖)
    {S : Set C} (hS : Dense S)
    (hagree : ∀ x ∈ S,
      Tendsto (fun n ↦ ‖f n x - g n x‖) atTop (nhds 0))
    (x : C) :
    Tendsto (fun n ↦ ‖f n x - g n x‖) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨b, hbS, hxb_dist⟩ :=
    Metric.mem_closure_iff.mp (hS x) (ε / 8) (by positivity)
  have hxb : ‖x - b‖ < ε / 8 := by
    rwa [← dist_eq_norm]
  have hsum : b + (x - b) = x := by abel
  obtain ⟨Nf, hNf⟩ := Metric.tendsto_atTop.mp
    (hfadd b (x - b)) (ε / 8) (by positivity)
  obtain ⟨Ng, hNg⟩ := Metric.tendsto_atTop.mp
    (hgadd b (x - b)) (ε / 8) (by positivity)
  obtain ⟨Na, hNa⟩ := Metric.tendsto_atTop.mp
    (hagree b hbS) (ε / 4) (by positivity)
  refine ⟨max Nf (max Ng Na), fun n hn ↦ ?_⟩
  have hnF : Nf ≤ n := le_trans (le_max_left _ _) hn
  have hnG : Ng ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnA : Na ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hfdefect : ‖f n (b + (x - b)) - f n b - f n (x - b)‖ < ε / 8 := by
    have := hNf n hnF
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using this
  have hgdefect : ‖g n (b + (x - b)) - g n b - g n (x - b)‖ < ε / 8 := by
    have := hNg n hnG
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using this
  have habagree : ‖f n b - g n b‖ < ε / 4 := by
    have := hNa n hnA
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using this
  have hfxb : ‖f n x - f n b‖ < ε / 4 := by
    rw [← hsum]
    calc
      ‖f n (b + (x - b)) - f n b‖ =
          ‖(f n (b + (x - b)) - f n b - f n (x - b)) + f n (x - b)‖ := by
            congr 1
            abel
      _ ≤ ‖f n (b + (x - b)) - f n b - f n (x - b)‖ +
          ‖f n (x - b)‖ := norm_add_le _ _
      _ < ε / 8 + ε / 8 :=
        add_lt_add hfdefect ((hfcontract n (x - b)).trans_lt hxb)
      _ = ε / 4 := by ring
  have hgxb : ‖g n b - g n x‖ < ε / 4 := by
    rw [norm_sub_rev, ← hsum]
    calc
      ‖g n (b + (x - b)) - g n b‖ =
          ‖(g n (b + (x - b)) - g n b - g n (x - b)) + g n (x - b)‖ := by
            congr 1
            abel
      _ ≤ ‖g n (b + (x - b)) - g n b - g n (x - b)‖ +
          ‖g n (x - b)‖ := norm_add_le _ _
      _ < ε / 8 + ε / 8 :=
        add_lt_add hgdefect ((hgcontract n (x - b)).trans_lt hxb)
      _ = ε / 4 := by ring
  have htotal : ‖f n x - g n x‖ < ε := by
    calc
      ‖f n x - g n x‖ =
          ‖(f n x - f n b) + (f n b - g n x)‖ := by
        congr 1
        abel
      _ ≤ ‖f n x - f n b‖ + ‖f n b - g n x‖ := norm_add_le _ _
      _ ≤ ‖f n x - f n b‖ +
          (‖f n b - g n b‖ + ‖g n b - g n x‖) := by
        have hmiddle : ‖f n b - g n x‖ ≤
            ‖f n b - g n b‖ + ‖g n b - g n x‖ := by
          calc
            ‖f n b - g n x‖ =
                ‖(f n b - g n b) + (g n b - g n x)‖ := by
              congr 1
              abel
            _ ≤ ‖f n b - g n b‖ + ‖g n b - g n x‖ := norm_add_le _ _
        simpa only [add_comm] using
          add_le_add_left hmiddle ‖f n x - f n b‖
      _ < ε / 4 + (ε / 4 + ε / 4) :=
        add_lt_add hfxb (add_lt_add habagree hgxb)
      _ < ε := by linarith
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using htotal

omit [NormedAddCommGroup C] in
/-- An error bound on the first `n` elements of a dense sequence gives
pointwise convergence on that dense sequence. -/
theorem tendsto_on_denseSequence_of_initial_bounds
    (s : ℕ → C) (f g : ℕ → C → E)
    (hinitial : ∀ n j, j ≤ n →
      ‖f n (s j) - g n (s j)‖ ≤ (1 : ℝ) / (n + 1))
    (j : ℕ) :
    Tendsto (fun n ↦ ‖f n (s j) - g n (s j)‖) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ε hε
  refine ⟨max N j, fun n hn ↦ ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hjn : j ≤ n := le_trans (le_max_right _ _) hn
  have hbound := hinitial n j hjn
  have hsmall : (1 : ℝ) / (n + 1) < ε := by
    have := hN n hnN
    have hnonneg : (0 : ℝ) ≤ (1 : ℝ) / (n + 1) := by positivity
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using this
  have hlt := hbound.trans_lt hsmall
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using hlt

/-- Expanding finite control on a dense sequence, contractivity, and
asymptotic additivity imply asymptotic compatibility everywhere.  This is the
completion step used after Shulman's finite commutant-unitary correction. -/
theorem tendsto_norm_sub_of_initial_dense_controls
    (s : ℕ → C) (hs : DenseRange s)
    (f g : ℕ → C → E)
    (hfadd : ∀ x y : C,
      Tendsto (fun n ↦ ‖f n (x + y) - f n x - f n y‖) atTop (nhds 0))
    (hgadd : ∀ x y : C,
      Tendsto (fun n ↦ ‖g n (x + y) - g n x - g n y‖) atTop (nhds 0))
    (hfcontract : ∀ n x, ‖f n x‖ ≤ ‖x‖)
    (hgcontract : ∀ n x, ‖g n x‖ ≤ ‖x‖)
    (hinitial : ∀ n j, j ≤ n →
      ‖f n (s j) - g n (s j)‖ ≤ (1 : ℝ) / (n + 1))
    (x : C) :
    Tendsto (fun n ↦ ‖f n x - g n x‖) atTop (nhds 0) := by
  apply tendsto_norm_sub_of_dense f g hfadd hgadd hfcontract hgcontract
    (S := Set.range s) hs
  rintro _ ⟨j, rfl⟩
  exact tendsto_on_denseSequence_of_initial_bounds s f g hinitial j

/-- Closed universal form of the dense compatibility theorem. -/
def InitialDenseControlsForceCompatibility : Prop :=
  ∀ {C : Type u} {E : Type v}
    [NormedAddCommGroup C] [NormedAddCommGroup E]
    (s : ℕ → C), DenseRange s →
    ∀ (f g : ℕ → C → E),
      (∀ x y : C,
        Tendsto (fun n ↦ ‖f n (x + y) - f n x - f n y‖) atTop (nhds 0)) →
      (∀ x y : C,
        Tendsto (fun n ↦ ‖g n (x + y) - g n x - g n y‖) atTop (nhds 0)) →
      (∀ n x, ‖f n x‖ ≤ ‖x‖) → (∀ n x, ‖g n x‖ ≤ ‖x‖) →
      (∀ n j, j ≤ n →
        ‖f n (s j) - g n (s j)‖ ≤ (1 : ℝ) / (n + 1)) →
      ∀ x : C, Tendsto (fun n ↦ ‖f n x - g n x‖) atTop (nhds 0)

/-- Expanding finite control on a dense sequence forces full asymptotic
compatibility. -/
theorem initialDenseControlsForceCompatibility :
    InitialDenseControlsForceCompatibility := by
  intro C E _ _ s hs f g hfadd hgadd hfcontract hgcontract hinitial x
  exact tendsto_norm_sub_of_initial_dense_controls s hs f g hfadd hgadd
    hfcontract hgcontract hinitial x

end

end ShulmanDenseCompatibility
end GroupApproximation

#audit_closed_axioms GroupApproximation.ShulmanDenseCompatibility.initialDenseControlsForceCompatibility
