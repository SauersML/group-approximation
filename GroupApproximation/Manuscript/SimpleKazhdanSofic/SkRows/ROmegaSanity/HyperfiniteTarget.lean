import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.ROmegaSanity.UltrapowerTraceState
import GroupApproximation.Analysis.MatrixUltraproductToHyperfiniteUltrapower
import GroupApproximation.Meta.AxiomGuard

/-!
# `𝓡^ω` is a non-degenerate target

Lane `sk-rows-08` (R^ω target non-vacuity).  `simple_kazhdan_sofic_group.tex`, subsection
"Brown's formulation":

> (tex 345–348) It is LEF, so it is sofic … and hyperlinear …, and $L(G)$ embeds in
> $\mathcal R^\omega$~\cite{Kirchberg,Radulescu},~\cite[Proposition~7.1]{Ozawa}.

The corpus target is `Hyperfinite.HyperfiniteUltrapower ω`, the abbreviation
`TracialUltrapower.Ultrapower Hyperfinite.hyperfiniteTracialVector ω`
(`Analysis/MatrixUltraproductToHyperfiniteUltrapower.lean:45–49`), with trace
`Hyperfinite.hyperfiniteUltratrace ω`.  An "embedding into `𝓡^ω`" would say nothing if that
algebra were the zero algebra.  This module rules that out.

* `hyperfiniteUltratrace_one`: the normalized trace of the identity is `1` at every coordinate,
  so its ultralimit is `1`.
* `hyperfiniteUltrapower_nontrivial`: hence `1 ≠ 0` in `𝓡^ω`.  The lane printed the hypothesis
  `ω ≤ cofinite`, but the argument does not use it, so the theorem is stated for every
  ultrafilter.  That is a stronger statement.
* `hyperfiniteUltratraceState`: the ultratrace is a faithful tracial state on `𝓡^ω`.
* `manuscriptSentence_injectiveStarHomToROmegaTraceState`: an injective unital `⋆`-homomorphism
  `Φ : A → 𝓡^ω` has a nonzero (nontrivial) domain, and `a ↦ trω (Φ a)` is a faithful tracial
  state on `A`.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity

noncomputable section

/-- **`trω 1 = 1` on `𝓡^ω`.** -/
theorem hyperfiniteUltratrace_one (ω : Ultrafilter ℕ) :
    Hyperfinite.hyperfiniteUltratrace ω 1 = 1 :=
  TracialUltrapower.ultratrace_one Hyperfinite.hyperfiniteTracialVector ω

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity.hyperfiniteUltratrace_one

/-- **`𝓡^ω` is nontrivial**, for every ultrafilter `ω` on `ℕ`. -/
theorem hyperfiniteUltrapower_nontrivial (ω : Ultrafilter ℕ) :
    Nontrivial (Hyperfinite.HyperfiniteUltrapower ω) :=
  ultrapower_nontrivial Hyperfinite.hyperfiniteTracialVector ω

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity.hyperfiniteUltrapower_nontrivial

/-- **The ultratrace of `𝓡^ω` is a faithful tracial state.** -/
def hyperfiniteUltratraceState (ω : Ultrafilter ℕ) :
    FaithfulTracialState (Hyperfinite.HyperfiniteUltrapower ω) :=
  ultratraceTracialState Hyperfinite.hyperfiniteTracialVector ω

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity.hyperfiniteUltratraceState

theorem hyperfiniteUltratraceState_apply (ω : Ultrafilter ℕ)
    (x : Hyperfinite.HyperfiniteUltrapower ω) :
    hyperfiniteUltratraceState ω x = Hyperfinite.hyperfiniteUltratrace ω x :=
  rfl

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity.hyperfiniteUltratraceState_apply

/-- **Injective `⋆`-homomorphisms into `𝓡^ω` preserve the trace state.**  For an injective
unital `⋆`-homomorphism `Φ : A → 𝓡^ω`, the algebra `A` is nontrivial, and `a ↦ trω (Φ a)` is a
faithful tracial state on `A`. -/
theorem manuscriptSentence_injectiveStarHomToROmegaTraceState {A : Type*} [Ring A] [StarRing A]
    [Algebra ℂ A] (ω : Ultrafilter ℕ) (Φ : A →⋆ₐ[ℂ] Hyperfinite.HyperfiniteUltrapower ω)
    (hΦ : Function.Injective Φ) :
    Nontrivial A ∧
      ∃ t : FaithfulTracialState A, ∀ a : A, t a = Hyperfinite.hyperfiniteUltratrace ω (Φ a) := by
  haveI := hyperfiniteUltrapower_nontrivial ω
  exact ⟨nontrivial_of_starAlgHom Φ,
    pullbackTracialState (hyperfiniteUltratraceState ω) Φ hΦ, fun _ ↦ rfl⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity.manuscriptSentence_injectiveStarHomToROmegaTraceState

/-- **Non-vacuity of the `𝓡^ω` target**, in one statement: for every ultrafilter `ω` on `ℕ`,
`𝓡^ω` is nontrivial, its ultratrace takes the value `1` at `1`, and it is a faithful tracial
state. -/
theorem manuscriptSentence_hyperfiniteUltrapowerNonvacuous (ω : Ultrafilter ℕ) :
    Nontrivial (Hyperfinite.HyperfiniteUltrapower ω) ∧
      Hyperfinite.hyperfiniteUltratrace ω 1 = 1 ∧
      ∃ t : FaithfulTracialState (Hyperfinite.HyperfiniteUltrapower ω),
        ∀ x, t x = Hyperfinite.hyperfiniteUltratrace ω x :=
  ⟨hyperfiniteUltrapower_nontrivial ω, hyperfiniteUltratrace_one ω,
    hyperfiniteUltratraceState ω, hyperfiniteUltratraceState_apply ω⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity.manuscriptSentence_hyperfiniteUltrapowerNonvacuous

end

end GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity
