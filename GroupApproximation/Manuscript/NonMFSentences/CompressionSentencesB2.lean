import GroupApproximation.Manuscript.NonMFSentences.CompressionSentencesB
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:normal-kazhdan`'s `τ` as a continuous linear functional on `𝒬_r`

`CompressionSentencesB.lean` proves the printed `τ = lim_ω tr_{r_n}` well
defined on representatives of the operator-norm corona `𝒬_r`
(`NormMatrixCStarCorona`) and reuses `Analysis/TracialMatrixUltraproduct.lean`
for its linearity, unit, positivity and traciality, again at the level of
representatives.  This file descends `τ` to a genuine continuous linear
functional `𝒬_r →L[ℂ] ℂ`, which the printed sentences after it need: "the two
states `τ∘π` and `χ` agree on every `u_k`, hence by linearity on the dense
subalgebra `ℂ[K]`, hence on `C*_max(K)`" reads two *functions* out of a
quotient agreeing everywhere by density, and that only typechecks once `τ`
is an honest function of the corona class, not merely a fact about
representatives.

The construction mirrors `Analysis/TracialMatrixUltraproduct.lean`'s own
`ultratrace`/`ultratraceLinearMap` exactly (`QuotientAddGroup.lift` off the
null ideal, then a linear wrapper by induction on the quotient), substituting
the operator-norm null ideal `nullMatrixSequenceIdeal · cofinite` for that
file's Hilbert--Schmidt one, and this file's own well-definedness lemma
(`manuscriptSentence_ultrafilterNormalizedTraceWellDefined`) for that file's.
Boundedness — the last ingredient before `LinearMap.mkContinuous` — is the
generic quotient-norm fact `Submodule.Quotient.norm_mk_lt`, applied the same
way `Analysis/NormMatrixCorona.lean`'s own (private) quotient-norm lemmas are.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ)

/-- The ultrafilter-limit normalized trace on bounded matrix sequences,
packaged as an additive monoid homomorphism, ready to descend through the
operator-norm null ideal. -/
def seqOpTraceHom : BoundedMatrixSequence (fun n ↦ X n) →+ ℂ where
  toFun := TracialUltraproduct.seqUltratrace X ω
  map_zero' := TracialUltraproduct.seqUltratrace_zero X ω
  map_add' := TracialUltraproduct.seqUltratrace_add X ω

@[simp] theorem seqOpTraceHom_apply (a : BoundedMatrixSequence (fun n ↦ X n)) :
    seqOpTraceHom X ω a = TracialUltraproduct.seqUltratrace X ω a := rfl

/-- **The operator-norm null ideal is in the kernel of `seqOpTraceHom`.**  The
quotient-descent hypothesis `QuotientAddGroup.lift` needs, proved from
`manuscriptSentence_ultrafilterNormalizedTraceWellDefined` applied against the
zero class. -/
theorem nullMatrixSequenceIdeal_le_seqOpTrace_ker
    (hω : (ω : Filter ℕ) ≤ cofinite) :
    (nullMatrixSequenceIdeal (fun n ↦ X n) cofinite).toAddSubgroup ≤
      (seqOpTraceHom X ω).ker := by
  intro a ha
  change TracialUltraproduct.seqUltratrace X ω a = 0
  have hnull : IsNullMatrixSequence (fun n ↦ X n) cofinite a := ha
  have hmk0 : normMatrixCStarCoronaMk (fun n ↦ X n) a
      = normMatrixCStarCoronaMk (fun n ↦ X n) 0 := by
    rw [RingHom.map_zero (normMatrixCStarCoronaMk (fun n ↦ X n))]
    exact (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) a).mpr hnull
  rw [manuscriptSentence_ultrafilterNormalizedTraceWellDefined X ω hω hmk0]
  exact TracialUltraproduct.seqUltratrace_zero X ω

/-- **`τ` on `𝒬_r`, as an additive homomorphism.**  Sends the class of `a` to
`lim_ω tr_{X n}(a n)`. -/
def ultrafilterNormalizedTraceAdd (hω : (ω : Filter ℕ) ≤ cofinite) :
    NormMatrixCStarCorona (fun n ↦ X n) →+ ℂ := by
  unfold NormMatrixCStarCorona
  exact QuotientAddGroup.lift
    (nullMatrixSequenceIdeal (fun n ↦ X n) cofinite).toAddSubgroup
    (seqOpTraceHom X ω) (nullMatrixSequenceIdeal_le_seqOpTrace_ker X ω hω)

@[simp] theorem ultrafilterNormalizedTraceAdd_mk
    (hω : (ω : Filter ℕ) ≤ cofinite) (a : BoundedMatrixSequence (fun n ↦ X n)) :
    ultrafilterNormalizedTraceAdd X ω hω
        (normMatrixCStarCoronaMk (fun n ↦ X n) a)
      = TracialUltraproduct.seqUltratrace X ω a := by
  unfold ultrafilterNormalizedTraceAdd normMatrixCStarCoronaMk NormMatrixCStarCorona
  exact QuotientAddGroup.lift_mk _ _ _

theorem ultrafilterNormalizedTraceAdd_smul (hω : (ω : Filter ℕ) ≤ cofinite)
    (c : ℂ) (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    ultrafilterNormalizedTraceAdd X ω hω (c • x)
      = c * ultrafilterNormalizedTraceAdd X ω hω x := by
  unfold NormMatrixCStarCorona at x
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    change ultrafilterNormalizedTraceAdd X ω hω
        (normMatrixCStarCoronaMk (fun n ↦ X n) (c • a))
      = c * ultrafilterNormalizedTraceAdd X ω hω
        (normMatrixCStarCoronaMk (fun n ↦ X n) a)
    rw [ultrafilterNormalizedTraceAdd_mk, ultrafilterNormalizedTraceAdd_mk]
    exact TracialUltraproduct.seqUltratrace_smul X ω c a

/-- **`τ` on `𝒬_r`, as a complex-linear functional.** -/
def ultrafilterNormalizedTraceLinear (hω : (ω : Filter ℕ) ≤ cofinite) :
    NormMatrixCStarCorona (fun n ↦ X n) →ₗ[ℂ] ℂ where
  toFun := ultrafilterNormalizedTraceAdd X ω hω
  map_add' := map_add (ultrafilterNormalizedTraceAdd X ω hω)
  map_smul' c x := by
    change ultrafilterNormalizedTraceAdd X ω hω (c • x)
      = c * ultrafilterNormalizedTraceAdd X ω hω x
    exact ultrafilterNormalizedTraceAdd_smul X ω hω c x

@[simp] theorem ultrafilterNormalizedTraceLinear_apply
    (hω : (ω : Filter ℕ) ≤ cofinite) (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    ultrafilterNormalizedTraceLinear X ω hω x
      = ultrafilterNormalizedTraceAdd X ω hω x := rfl

/-- **`|τ(x)| ≤ ‖x‖`, at the quotient.**  The printed inequality
`|tr_{r_n}(x)| ≤ ‖x‖` survives both the ultralimit
(`TracialUltraproduct.norm_seqUltratrace_le`) and the quotient, by the
standard `Submodule.Quotient.norm_mk_lt` approximation-by-representatives
argument. -/
theorem norm_ultrafilterNormalizedTraceAdd_le (hω : (ω : Filter ℕ) ≤ cofinite)
    (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    ‖ultrafilterNormalizedTraceAdd X ω hω x‖ ≤ ‖x‖ := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hrep : ∃ a : BoundedMatrixSequence (fun n ↦ X n),
      normMatrixCStarCoronaMk (fun n ↦ X n) a = x ∧ ‖a‖ < ‖x‖ + ε := by
    unfold NormMatrixCStarCorona at x
    unfold normMatrixCStarCoronaMk NormMatrixCStarCorona
    obtain ⟨a, ha_eq, ha_lt⟩ := Submodule.Quotient.norm_mk_lt x hε
    exact ⟨a, ha_eq, ha_lt⟩
  obtain ⟨a, rfl, ha_lt⟩ := hrep
  rw [ultrafilterNormalizedTraceAdd_mk]
  exact (TracialUltraproduct.norm_seqUltratrace_le X ω a).trans ha_lt.le

/-- **`τ` on `𝒬_r`, as a continuous linear functional.**  The printed `τ`, at
last a genuine function of the corona class rather than a fact about
representatives, ready for `maximalGroupCStar_ext_of_generator`. -/
def ultrafilterNormalizedTraceCLM (hω : (ω : Filter ℕ) ≤ cofinite) :
    NormMatrixCStarCorona (fun n ↦ X n) →L[ℂ] ℂ :=
  LinearMap.mkContinuous (ultrafilterNormalizedTraceLinear X ω hω) 1
    (fun x ↦ by
      rw [one_mul, ultrafilterNormalizedTraceLinear_apply]
      exact norm_ultrafilterNormalizedTraceAdd_le X ω hω x)

@[simp] theorem ultrafilterNormalizedTraceCLM_apply
    (hω : (ω : Filter ℕ) ≤ cofinite) (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    ultrafilterNormalizedTraceCLM X ω hω x
      = ultrafilterNormalizedTraceAdd X ω hω x := rfl

end

end NonMFSentences
end Manuscript
end GroupApproximation
