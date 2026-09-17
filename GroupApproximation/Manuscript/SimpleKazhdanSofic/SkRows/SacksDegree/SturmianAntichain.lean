import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SacksDegree.WordProblemDegree
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemsCorollaryAssembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SturmianComputability
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ContinuedFractionRepresentative
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SturmianSubshiftSetting
import GroupApproximation.Meta.AxiomGuard

/-!
# The word problem degree map onto a Sacks antichain

`simple_kazhdan_sofic_group.tex`, proof of `cor:wp`, tex l.719–721:

> By a construction of Sacks, the Turing degrees contain an antichain of size
> continuum~\cite[Chapter~V]{Odifreddi}, and the groups $G_{X_\alpha}$ with $\alpha$ of these
> degrees are as claimed.

`manuscriptSentence_sacksWordProblemDegreeAntichain` states the whole sentence in Mathlib's
`TuringDegree`. There is a continuum set `S` of slopes in `(0,1)`, all irrational with infinite
minimal Sturmian subshifts `X_α`. On `S` the map `α ↦ deg WP(G_{X_α})` is injective, and its image
is an antichain of `TuringDegree` of cardinality `𝔠`. For `α, β ∈ S`, `G_{X_α}` embeds in `G_{X_β}`
only if `α = β`.

## Route

* The Sacks family `F` (`charDegree_antichain_family`, from `printedTuringAntichainContinuum`).
* Each `B` is the degree of a continued fraction `α B = [0; 1 + χ_B(0), …]` in `(0,1)`
  (`printedContinuedFractionRepresentative`), and `S = α '' F`.
* `deg WP(G_{X_{α B}}) = deg B` (`hWP`): `WP(G_X) ≡_T L(X)` (`printedWordProblemDegreeEqLanguage`),
  `L(X_α) ≡_T α` (`SturmianComputability`), `α B ≡_T B`.
* Injectivity and incomparability pull back to `F` along `hWP`. An embedding reduces word problems
  (`printedWordProblemReducesUnderEmbedding`), so it forces `deg B ≤ deg C`, hence `B = C`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SkRows
namespace SacksDegree

open Set SturmianComputability

/-- **Proof of `cor:wp`, tex l.719–721, whole sentence**, in Mathlib's `TuringDegree`: a continuum
set `S` of slopes of infinite minimal Sturmian subshifts on which `α ↦ deg WP(G_{X_α})` is injective
onto an antichain of size continuum, and none of the groups `G_{X_α}`, `α ∈ S`, embeds in another. -/
theorem manuscriptSentence_sacksWordProblemDegreeAntichain :
    ∃ S : Set ℝ, Cardinal.mk S = Cardinal.continuum ∧
      (∀ α ∈ S, Irrational α ∧ 0 < α ∧ α < 1 ∧ (sturmianSubshift α).carrier.Infinite ∧
        IsMinimal (sturmianSubshift α)) ∧
      InjOn sturmianWordProblemDegree S ∧
      IsAntichain (· ≤ ·) (sturmianWordProblemDegree '' S) ∧
      Cardinal.mk (sturmianWordProblemDegree '' S) = Cardinal.continuum ∧
      ∀ α ∈ S, ∀ β ∈ S,
        (∃ ψ : G (sturmianSubshift α) →* G (sturmianSubshift β), Function.Injective ψ) →
          α = β := by
  classical
  haveI : Finite (Coeff Bool) := Finite.of_equiv _ (Coeff.equivOption Bool).symm
  obtain ⟨F, hF, hinjF, hle⟩ := charDegree_antichain_family
  have hdeg : ∀ B : Set ℕ, ∃ α : ℝ, Irrational α ∧ 0 < α ∧ α < 1 ∧
      TuringEquivalent (slopeOracle α) (charOracle B) := fun B => by
    obtain ⟨α, hcf, hirr, heq⟩ := printedContinuedFractionRepresentative B
    have hfl : ⌊α⌋ = 0 := by
      have h := hcf.1
      rw [GenContFract.of_h_eq_floor] at h
      exact_mod_cast h
    obtain ⟨h0, h1⟩ := Int.floor_eq_zero_iff.1 hfl
    exact ⟨α, hirr, lt_of_le_of_ne h0 (Ne.symm hirr.ne_zero), h1, heq⟩
  choose α hirr hpos hlt hχ using hdeg
  have hmin : ∀ B, (sturmianSubshift (α B)).carrier.Infinite ∧ IsMinimal (sturmianSubshift (α B)) :=
    fun B => printedSturmianSubshiftInfiniteIsMinimal (α B) (hirr B) (hpos B) (hlt B)
  have hWP : ∀ B, sturmianWordProblemDegree (α B) = charDegree B := fun B => by
    have hWL := printedWordProblemDegreeEqLanguage Bool (sturmianSubshift (α B))
      (hmin B).1.to_subtype (hmin B).2
    have hLα : TuringEquivalent (languageOracle (sturmianSubshift (α B))) (slopeOracle (α B)) :=
      ⟨printedSlopeComputesSturmianLanguage (α B) (hirr B) (hpos B) (hlt B),
        printedSturmianLanguageComputesSlope (α B) (hirr B) (hpos B) (hlt B)⟩
    exact (turingDegreeOf_eq_iff (wordProblemOracle (genValue (sturmianSubshift (α B))))
      (charOracle B)).2
        (TuringEquivalent.trans _ _ _ (TuringEquivalent.trans _ _ _ hWL hLα) (hχ B))
  have hαinj : InjOn α F := by
    intro B hB C hC h
    exact hinjF hB hC (by rw [← hWP B, ← hWP C, h])
  have hwpinj : InjOn sturmianWordProblemDegree (α '' F) := by
    rintro _ ⟨B, hB, rfl⟩ _ ⟨C, hC, rfl⟩ h
    have e : charDegree B = charDegree C := by
      rw [← hWP B, ← hWP C]
      exact h
    exact congrArg α (hinjF hB hC e)
  refine ⟨α '' F, ?_, ?_, hwpinj, ?_, ?_, ?_⟩
  · rw [Cardinal.mk_image_eq_of_injOn _ _ hαinj, hF]
  · rintro _ ⟨B, -, rfl⟩
    exact ⟨hirr B, hpos B, hlt B, hmin B⟩
  · rintro _ ⟨_, ⟨B, hB, rfl⟩, rfl⟩ _ ⟨_, ⟨C, hC, rfl⟩, rfl⟩ hne hBC
    have hBC' : charDegree B ≤ charDegree C := by
      rw [← hWP B, ← hWP C]
      exact hBC
    exact hne (congrArg (fun D => sturmianWordProblemDegree (α D)) (hle B hB C hC hBC'))
  · rw [Cardinal.mk_image_eq_of_injOn _ _ hwpinj, Cardinal.mk_image_eq_of_injOn _ _ hαinj, hF]
  · rintro _ ⟨B, hB, rfl⟩ _ ⟨C, hC, rfl⟩ ⟨ψ, hψ⟩
    have hred := printedWordProblemReducesUnderEmbedding (G (sturmianSubshift (α B)))
      (G (sturmianSubshift (α C))) (Gen Bool) (Gen Bool) (genValue (sturmianSubshift (α C)))
      (genValue (sturmianSubshift (α B))) ψ hψ (closure_range_genValue _) (closure_range_genValue _)
    have hBC : charDegree B ≤ charDegree C := by
      rw [← hWP B, ← hWP C]
      exact (turingDegreeOf_le_iff (wordProblemOracle (genValue (sturmianSubshift (α B))))
        (wordProblemOracle (genValue (sturmianSubshift (α C))))).2 hred
    exact congrArg α (hle B hB C hC hBC)

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SacksDegree.manuscriptSentence_sacksWordProblemDegreeAntichain

end SacksDegree
end SkRows
end SimpleKazhdanSofic
end GroupApproximation
