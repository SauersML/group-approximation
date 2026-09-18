import GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.Stage
import GroupApproximation.Analysis.QuasidiagonalTraceGeneratorDense
import GroupApproximation.Analysis.HNNTraceTracialStateContinuous
import GroupApproximation.Meta.AxiomGuard

/-!
# AF algebras: every tracial state is quasidiagonal

Lane `nm-tww-04`. **Endpoint**:
`isQuasidiagonalTrace_of_afPresentation_of_multimatrixTraceAmplification`. For every
`P : AFPresentation A` and every tracial state `τ` on `A`, `τ` is quasidiagonal, given
the interface `MultimatrixTraceAmplificationStatement` of lane `nm-tww-03`.

## Route

1. At each stage `n`, `exists_stage` gives a ucp matrix map `φₙ` that is exactly
   multiplicative on `ιₙ(Bₙ)` and satisfies
   `‖τ(ιₙ b) − tr(φₙ(ιₙ b))‖ ≤ ‖ιₙ b‖/(n+2)`.
2. `φₙ` is contractive (`Quasidiagonal.ucp_norm_le`), and `τ` is continuous
   (`HNNTrace.tracialStateCLM`).
3. Generators: `S = ⋃ₘ ιₘ(Bₘ)`. It is dense, so its span is dense. If `a = ιₘ b` and
   `n ≥ m`, then `a ∈ ιₙ(Bₙ)` (`AFPresentation.range_subset`).
   * For two generators, the multiplicative defect is `0` once `n` passes both of
     their stages.
   * For one generator, the trace defect is at most `‖a‖/(n+2) ≤ ‖a‖/(n+1) → 0`.
4. `AmenableExtensionTrace.quasidiagonalTraceModel_of_dense_generators` assembles
   the model.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace AFQD

open Filter Quasidiagonal
open scoped Matrix.Norms.L2Operator

noncomputable section

attribute [local instance] matrixBlockCStarAlgebra multimatrixCStarAlgebra

variable {A : Type} [CStarAlgebra A]

/-- Every element of the generating set `⋃ₘ ιₘ(Bₘ)` lies in `ιₙ(Bₙ)` for all
large `n`. -/
theorem AFPresentation.eventually_mem_range (P : AFPresentation A) (a : A)
    (ha : a ∈ ⋃ m : ℕ, Set.range ⇑(P.embed m)) :
    ∃ m : ℕ, ∀ n : ℕ, m ≤ n →
      ∃ b : Multimatrix (P.blocks n) (P.sizes n), P.embed n b = a := by
  obtain ⟨m, hm⟩ := Set.mem_iUnion.1 ha
  exact ⟨m, fun n hmn ↦ P.range_subset hmn hm⟩

/-- **AF algebras: every tracial state is quasidiagonal**, relative to the
rational-amplification interface of lane `nm-tww-03`. -/
theorem isQuasidiagonalTrace_of_afPresentation_of_multimatrixTraceAmplification
    (h : MultimatrixTraceAmplificationStatement) (P : AFPresentation A)
    (τ : TracialState A) :
    IsQuasidiagonalTrace (fun a : A ↦ τ a) := by
  choose Y φ hone hcp hmulStage htrStage using exists_stage h P τ
  have hcontr : ∀ n a, ‖φ n a‖ ≤ ‖a‖ := fun n a ↦ ucp_norm_le (φ n) (hone n) (hcp n) a
  have hS : Dense (Submodule.span ℂ (⋃ m : ℕ, Set.range ⇑(P.embed m)) : Set A) :=
    P.dense.mono Submodule.subset_span
  have hmulS : ∀ a ∈ (⋃ m : ℕ, Set.range ⇑(P.embed m)),
      ∀ c ∈ (⋃ m : ℕ, Set.range ⇑(P.embed m)),
        Tendsto (fun n ↦ ‖φ n (a * c) - φ n a * φ n c‖) atTop (nhds 0) := by
    intro a ha c hc
    obtain ⟨m, hm⟩ := P.eventually_mem_range a ha
    obtain ⟨m', hm'⟩ := P.eventually_mem_range c hc
    have heq : ∀ᶠ n in atTop, ‖φ n (a * c) - φ n a * φ n c‖ = 0 := by
      filter_upwards [eventually_ge_atTop (max m m')] with n hn
      obtain ⟨b, hb⟩ := hm n (le_of_max_le_left hn)
      obtain ⟨b', hb'⟩ := hm' n (le_of_max_le_right hn)
      rw [← hb, ← hb', hmulStage n b b', sub_self, norm_zero]
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)
  have htraceS : ∀ a ∈ (⋃ m : ℕ, Set.range ⇑(P.embed m)),
      Tendsto (fun n ↦ ‖HNNTrace.tracialStateCLM τ a - normTrace (Y n) (φ n a)‖)
        atTop (nhds 0) := by
    intro a ha
    obtain ⟨m, hm⟩ := P.eventually_mem_range a ha
    have hlim : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) * ‖a‖) atTop (nhds 0) := by
      have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ‖a‖
      rwa [zero_mul] at h0
    refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop m] with n hn
    obtain ⟨b, hb⟩ := hm n hn
    have hstage := htrStage n b
    rw [hb] at hstage
    have hle : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    calc ‖HNNTrace.tracialStateCLM τ a - normTrace (Y n) (φ n a)‖
        = ‖τ a - normTrace (Y n) (φ n a)‖ := by rw [HNNTrace.tracialStateCLM_apply]
      _ ≤ 1 / ((n : ℝ) + 2) * ‖a‖ := hstage
      _ ≤ 1 / ((n : ℝ) + 1) * ‖a‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg a)
  exact ⟨AmenableExtensionTrace.quasidiagonalTraceModel_of_dense_generators φ hone hcp
    hcontr (HNNTrace.tracialStateCLM τ) (⋃ m : ℕ, Set.range ⇑(P.embed m)) hS hmulS
    htraceS⟩

end

end AFQD
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.AFPresentation.eventually_mem_range
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.isQuasidiagonalTrace_of_afPresentation_of_multimatrixTraceAmplification
