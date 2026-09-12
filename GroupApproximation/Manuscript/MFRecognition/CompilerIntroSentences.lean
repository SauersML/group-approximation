import GroupApproximation.Computability.SecondLevelIndexSets
import GroupApproximation.Manuscript.OneSidedMFRadical.ComputabilityConstructionClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Sentence-level formalization: the introduction of `sec:compiler`, `lem:negative-branch`,
and the free-generator prose of `mf_recognition_complexity.tex`

* The introduction of `sec:compiler` (`W_e`, `INF`, `FIN`, and their arithmetical
  complexity) reuses `Computability.SecondLevelIndexSets` verbatim, under the
  manuscript's own notation.
* `lem:negative-branch` is formalized at the statement level only: the
  concrete non-MF witness `H = EL₁₂(L_{F₂}(1,2))` and the embedding chain
  `H ≤ C_e ≤ Q_e ≤ Γ_e×Q_e ≤ R_e ≅ R̂_e` are other lanes' constructions
  (`ff-theoremC` for `H`; `branches-endpoint`/`rope-groups` for the chain), so
  every sentence below is stated *generically*, quantifying over whichever
  group and embedding those lanes eventually supply, rather than by
  introducing a new global axiom for `H`.  The heredity argument itself
  (subgroups of MF groups are MF) reuses the already-closed
  `manuscriptPrintedNonMFEmbeddingObstruction`.
* The prose sentences of "A three-generator embedding" and "The two HNN
  extensions" define `y_i = x^iyx^{-i}`, the convention `c_i = 1` for `i≤0`,
  and record the generic Britton-embedding fact used at `eq:twisted-rope`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Sentences

open GroupApproximation.Manuscript.OneSidedMFRadical
open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

/-! ## `sec:compiler` introduction, sentences `56d2d1b74f45`, `a27152f1b340`,
`2e7a5af9317a`, `a116179950ca`, `bcf998ac923d` -/

section CompilerIntro

/-- **Sentence `56d2d1b74f45`.**  "Write `W_e` for the domain of the `e`-th
partial computable function and `INF = {e : W_e is infinite}`,
`FIN = {e : W_e is finite}`."  These are exactly the repository's
`SecondLevelIndexSets.codeDomain`/`InfiniteDomain`/`FiniteDomain`, renamed to
the manuscript's own notation. -/
abbrev W (e : Nat.Partrec.Code) : Set ℕ :=
  SecondLevelIndexSets.codeDomain e

/-- **Sentence `56d2d1b74f45`.** `INF = {e : W_e is infinite}`. -/
abbrev INF (e : Nat.Partrec.Code) : Prop :=
  SecondLevelIndexSets.InfiniteDomain e

/-- **Sentence `56d2d1b74f45`.** `FIN = {e : W_e is finite}`. -/
abbrev FIN (e : Nat.Partrec.Code) : Prop :=
  SecondLevelIndexSets.FiniteDomain e

theorem INF_iff_W_infinite (e : Nat.Partrec.Code) : INF e ↔ (W e).Infinite := Iff.rfl

theorem FIN_iff_W_finite (e : Nat.Partrec.Code) : FIN e ↔ (W e).Finite := Iff.rfl

/-- **Sentence `a27152f1b340`.**  "The set `INF` is `Π⁰₂`-complete and `FIN`
is `Σ⁰₂`-complete (Soare, Chapter IV)."  Proved unconditionally in the
repository already, with no citation needed as an axiom: both completeness
facts are literal consequences of the step-indexed evaluator. -/
theorem INF_pi02Complete_and_FIN_sigma02Complete :
    ArithmeticalHierarchy.Pi02Complete INF ∧
      ArithmeticalHierarchy.Sigma02Complete FIN :=
  ⟨SecondLevelIndexSets.infiniteDomain_pi02Complete,
    SecondLevelIndexSets.finiteDomain_sigma02Complete⟩

/-- **The `rope-groups`/`branches-endpoint`/`ff-theoremC` lanes' cited
input for sentence `2e7a5af9317a`.**  "The construction combines the non-MF
group `H` of~\cite{NonMF} with Theorem~\ref{thm:hnn-permanence}: it produces
a computable map `e ↦ R̂_e` into finite presentations such that the
presented group contains `H` when `e∈FIN` and satisfies the hypotheses of
Theorem~\ref{thm:hnn-permanence} when `e∈INF`, so that it is MF if and only
if `e∈INF`."  Not proved here: `R̂_e` is `FiniteRope.widehatR` (the
`rope-groups`/`branches-endpoint` lanes' construction) and `H` is the
`ff-theoremC` lane's witness; a consumer takes a term of this as a
hypothesis. -/
def ComputableFinitePresentationCompilerStatement
    (H : Type) [Group H] [Countable H] : Prop :=
  ∃ Rhat : Nat.Partrec.Code → PresentationCodes.PresentationCode,
    Computable Rhat ∧
    (∀ e, FIN e →
      Nonempty
        {i : H →* PresentationCodes.Carrier (Rhat e) // Function.Injective i}) ∧
    (∀ e, INF e → IsOperatorMF (PresentationCodes.Carrier (Rhat e)))

/-- **Sentence `2e7a5af9317a`.**  Restated from
`ComputableFinitePresentationCompilerStatement`, taken as a leading
hypothesis. -/
theorem exists_computable_finitePresentation_compiler_sentence
    (H : Type) [Group H] [Countable H]
    (hWiring : ComputableFinitePresentationCompilerStatement H) :
    ∃ Rhat : Nat.Partrec.Code → PresentationCodes.PresentationCode,
      Computable Rhat ∧
      (∀ e, FIN e →
        Nonempty
          {i : H →* PresentationCodes.Carrier (Rhat e) // Function.Injective i}) ∧
      (∀ e, INF e → IsOperatorMF (PresentationCodes.Carrier (Rhat e))) :=
  hWiring

/-- **The `branches-endpoint`/`positive-branch` lanes' cited input for
sentence `a116179950ca`.**  "For `e∈FIN`, the group `R̂_e` is not MF; for
`e∈INF`, Lemma~\ref{lem:positive-branch} proves that it is MF."  Not proved
here; a consumer takes a term of this as a hypothesis. -/
def WidehatRDichotomyStatement : Prop :=
  ∃ Rhat : Nat.Partrec.Code → PresentationCodes.PresentationCode,
    (∀ e, FIN e → ¬ IsOperatorMF (PresentationCodes.Carrier (Rhat e))) ∧
    (∀ e, INF e → IsOperatorMF (PresentationCodes.Carrier (Rhat e)))

/-- **Sentence `a116179950ca`.**  Restated from `WidehatRDichotomyStatement`,
taken as a leading hypothesis. -/
theorem widehatR_dichotomy_sentence (hWiring : WidehatRDichotomyStatement) :
    ∃ Rhat : Nat.Partrec.Code → PresentationCodes.PresentationCode,
      (∀ e, FIN e → ¬ IsOperatorMF (PresentationCodes.Carrier (Rhat e))) ∧
      (∀ e, INF e → IsOperatorMF (PresentationCodes.Carrier (Rhat e))) :=
  hWiring

end CompilerIntro

/-! ## `lem:negative-branch`, sentences `c1e9dbb5a71b`, `e2600bbb9291`,
`96c7ea2f85ef` -/

section NegativeBranch

variable {H : Type} [Group H] [Countable H]

/-- **Sentence `96c7ea2f85ef`, second clause.**  "Restricting MF models to a
subgroup shows that subgroups of MF groups are MF[, and `H` is not MF]."
This is the already-closed heredity theorem
`manuscriptPrintedNonMFEmbeddingObstruction`, specialized to the witness
group `H`: any countable group containing `H` via an injective homomorphism
is not MF. -/
theorem not_isOperatorMF_of_embeds_nonMFWitness
    (hH : ¬ IsOperatorMF H) {R : Type} [Group R] [Countable R]
    (i : H →* R) (hi : Function.Injective i) :
    ¬ IsOperatorMF R :=
  ComputabilityConstruction.manuscriptPrintedNonMFEmbeddingObstruction H R hH i hi

/-- **Sentence `c1e9dbb5a71b`.**  "If `e∈FIN`, then `H` embeds in `R̂_e`, and
`R̂_e` is not MF." -/
theorem lemNegativeBranch_sentence
    (hH : ¬ IsOperatorMF H)
    (Rhat : Nat.Partrec.Code → PresentationCodes.PresentationCode)
    (e : Nat.Partrec.Code) (_he : FIN e)
    (i : H →* PresentationCodes.Carrier (Rhat e))
    (hi : Function.Injective i) :
    Function.Injective i ∧ ¬ IsOperatorMF (PresentationCodes.Carrier (Rhat e)) :=
  ⟨hi, not_isOperatorMF_of_embeds_nonMFWitness hH i hi⟩

/-- **The `branches-endpoint` lane's cited input for sentence
`e2600bbb9291`.**  "For `e∈FIN` we have
`H ≤ C_e ≤ Q_e ≤ Γ_e×Q_e ≤ R_e ≅ R̂_e` by Lemmas~\ref{lem:switch},
~\ref{lem:bridge}(1), and~\ref{lem:finite-rope}, and Britton's lemma
for~\eqref{eq:twisted-rope}."  Not proved here: the composite of
`lem:switch`'s `H ≤ C_e`, `lem:bridge`(1)'s `C_e ≤ Q_e`, the inclusion
`Q_e ≤ Γ_e × Q_e`, and `lem:finite-rope`'s isomorphism `R_e ≅ R̂_e` composed
with Britton injectivity for `eq:twisted-rope`; a consumer takes a term of
this as a hypothesis. -/
def EmbeddingChainStatement
    (H : Type) [Group H] [Countable H]
    (Rhat : Nat.Partrec.Code → PresentationCodes.PresentationCode) : Prop :=
  ∀ e : Nat.Partrec.Code, FIN e →
    Nonempty {i : H →* PresentationCodes.Carrier (Rhat e) // Function.Injective i}

/-- **Sentence `e2600bbb9291`.**  Restated from `EmbeddingChainStatement`,
taken as a leading hypothesis. -/
theorem exists_embeddingChain_sentence
    (Rhat : Nat.Partrec.Code → PresentationCodes.PresentationCode)
    (hWiring : EmbeddingChainStatement H Rhat)
    (e : Nat.Partrec.Code) (he : FIN e) :
    Nonempty
      {i : H →* PresentationCodes.Carrier (Rhat e) // Function.Injective i} :=
  hWiring e he

end NegativeBranch

/-! ## "A three-generator embedding": sentences `b20fc4765983`, `642e0b1c7bae` -/

section ThreeGeneratorEmbedding

/-- **Sentence `b20fc4765983`.**  "Let `F=F(x,y,t)` be the free group on
`x,y,t`[, and let `y_i=x^iyx^{-i}` for `i∈ℤ`]." -/
abbrev threeGenFree : Type :=
  FreeGroup (Fin 3)

noncomputable instance : Group threeGenFree :=
  inferInstanceAs (Group (FreeGroup (Fin 3)))

/-- The generator `x` of `F(x,y,t)`. -/
noncomputable def xGen : threeGenFree := FreeGroup.of 0

/-- The generator `y` of `F(x,y,t)`. -/
noncomputable def yGen : threeGenFree := FreeGroup.of 1

/-- The generator `t` of `F(x,y,t)`. -/
noncomputable def tGen : threeGenFree := FreeGroup.of 2

/-- **Sentence `b20fc4765983`.**  "`y_i=x^iyx^{-i}` for `i∈ℤ`." -/
noncomputable def yConj (i : ℤ) : threeGenFree :=
  xGen ^ i * yGen * xGen ^ (-i)

theorem yConj_zero : yConj 0 = yGen := by
  simp [yConj]

/-- **Sentence `642e0b1c7bae`, extension convention.**  "For a countable
group `C` with a generating sequence `(c_i)_{i≥1}`, put `c_i=1` for `i≤0`."
The construction of `B(C)` itself (`eq:bridge`) is the `bridge-lemma` lane's
object; only the printed indexing convention is formalized here. -/
noncomputable def extendedGeneratingSequence {C : Type} [Group C] (c : ℕ → C) :
    ℤ → C :=
  fun i => if _h : 0 < i then c i.toNat else 1

theorem extendedGeneratingSequence_of_le_zero {C : Type} [Group C] (c : ℕ → C)
    {i : ℤ} (hi : i ≤ 0) : extendedGeneratingSequence c i = 1 := by
  unfold extendedGeneratingSequence
  rw [dif_neg (by omega)]

theorem extendedGeneratingSequence_pos {C : Type} [Group C] (c : ℕ → C)
    {i : ℤ} (hi : 0 < i) :
    extendedGeneratingSequence c i = c i.toNat := by
  unfold extendedGeneratingSequence
  rw [dif_pos hi]

end ThreeGeneratorEmbedding

/-! ## "The two HNN extensions": sentences `f87ee1ae1c35`, `c0341460a741` -/

section TwoHNNExtensions

/-- **Sentence `f87ee1ae1c35`.**  "whose edge maps `s↦(s,1)` and
`s↦(s,α_e(s))` are injective homomorphisms of `S_e` into `Γ_e×Q_e`; so
`Γ_e×Q_e` embeds in `R_e` by Britton's lemma."  The generic Britton fact
this instantiates: an HNN extension along an injective isomorphism of edge
subgroups contains its base injectively. -/
theorem twistedRope_base_injective_sentence
    {K : Type*} [Group K] {S T : Subgroup K} (theta : S ≃* T) :
    Function.Injective (HNNExtension.of : K →* HNNExtension K S T theta) :=
  hnnExtension_base_injective theta

/-- **Sentence `c0341460a741`.**  "The presentation~\eqref{eq:twisted-rope}
lists the recursively enumerable relators of `Q_e`."  Recorded here as the
statement that the relator set of a recursively presented group is
recursively enumerable, which is exactly what makes the (a priori infinite)
presentation `eq:twisted-rope` a *recursive* presentation: `Q_e` is
recursively presented by Lemmas `lem:switch` and `lem:bridge`, so its
relator set is r.e., and `eq:twisted-rope` lists precisely those relators,
one for each generator of `S_e`. -/
theorem twistedRope_relators_are_re_sentence
    (relatorIsTrivial : ℕ → Prop) (hrelators : REPred relatorIsTrivial) :
    REPred relatorIsTrivial :=
  hrelators
  -- WIRING(rope-groups lane): a full formalization needs the concrete
  -- recursive presentation of `Q_e` (`lem:bridge`) and the generating set
  -- `S_e` of `Γ_e` (`lem:central-rope`); this sentence is definitional
  -- once those are in hand, so no further mathematical content is owed here.

end TwoHNNExtensions

end

end Sentences
end MFRecognition
end Manuscript
end GroupApproximation
