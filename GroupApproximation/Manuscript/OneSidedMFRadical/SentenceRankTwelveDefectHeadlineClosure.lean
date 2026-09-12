import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceDoubleCommutatorExtractionClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.HeadlineTheorem

/-!
# Sentence closure for the rank-twelve defect and headline proof

Paper-facing wrappers for census rows 254--268.  Every proof is a definitional
unfolding or a composition of the unconditional rank-twelve declarations.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

open scoped commutatorElement

/-- The exact rank-twelve group is countable; expose the proved theorem as a
local instance for the two MF propositions below. -/
local instance sentenceRankTwelveCountable : Countable H := countable

/-- **Sentence 254.**  The three literal group elements used in the defect
calculation have exactly the printed elementary-root definitions. -/
theorem manuscriptSentence254_literalElements :
    c = elementaryRoot (3 : Fin 12) 4 (by decide) 1 ∧
      ell = elementaryRoot (1 : Fin 12) 2 (by decide) 1 ∧
      defect = elementaryRoot (0 : Fin 12) 2 (by decide) q :=
  ⟨rfl, rfl, rfl⟩

/-- **Sentence 255.**  The four displayed assertions of `prop:defect`. -/
theorem manuscriptSentence255_defectProposition : PropositionDefect :=
  manuscriptPropositionDefect

/-- **Sentence 256.**  The disjoint upper-left generators, and hence their
generated corner, commute with `c=e₃₄(1)`. -/
def Sentence256CentralizesCorner : Prop :=
  ∀ gamma ∈ corner, Commute c gamma

theorem manuscriptSentence256_centralizesCorner :
    Sentence256CentralizesCorner :=
  c_commutes_corner

/-- **Sentence 257.**  The moved mark is the exact product printed in
`eq:moved-mark`. -/
theorem manuscriptSentence257_movedMark :
    tau * c * tau⁻¹ = elementaryRoot (0 : Fin 12) 1 (by decide) q * c :=
  tau_conj_c

/-- **Sentence 258.**  Commuting away the second factor and applying the
elementary commutator relation gives the printed defect. -/
theorem manuscriptSentence258_defectCommutator :
    ⁅tau * c * tau⁻¹, ell⁆ = defect :=
  tau_c_commutator_ell

/-- **Sentence 259.**  The defect is nonidentity because its coefficient is
nonzero. -/
theorem manuscriptSentence259_defect_ne_one : defect ≠ 1 :=
  defect_ne_one

/-- **Sentence 260.**  The sandwiched elementary defect normally generates
the whole rank-twelve group. -/
theorem manuscriptSentence260_defectNormallyGenerates :
    Subgroup.normalClosure ({defect} : Set H) = ⊤ :=
  normalClosure_defect_eq_top

/-- **Sentence 261.**  The finitely generated coefficient algebra is
countable, and so is the exact elementary group. -/
theorem manuscriptSentence261_countability :
    Countable R ∧ Countable H :=
  ⟨inferInstance, countable⟩

/-- **Sentence 262.**  The coefficient algebra is of finite type and the
rank-twelve elementary group has property `(T)`. -/
theorem manuscriptSentence262_finiteType_and_propertyT :
    Algebra.FiniteType (ZMod 2) R ∧ HasKazhdanPropertyT.{0, 0} H :=
  ⟨inferInstance, hasKazhdanPropertyT⟩

/-- **Sentence 263.**  Compression and centrality put the explicit commutator
defect in the printed defect subgroup. -/
theorem manuscriptSentence263_defect_mem_printedDefect :
    defect ∈ printedDefect corner := by
  rw [← tau_c_commutator_ell]
  exact printedDefect_generator_mem corner tau_compresses_corner
    c_commutes_corner ell_mem_corner

/-- **Sentence 264.**  Normality plus normal generation saturates the printed
defect subgroup. -/
theorem manuscriptSentence264_printedDefect_eq_top :
    printedDefect corner = ⊤ :=
  printedDefect_eq_top_of_configuration printedDefectConfiguration

/-- **Sentence 265.**  The compression criterion gives full actual corona MF
radical for the exact group. -/
theorem manuscriptSentence265_fullRadical :
    actualCoronaMFResidual H = ⊤ :=
  rankTwelve_actualCoronaMFResidual_eq_top

/-- **Sentence 266.**  Independently, the exact group is nontrivial and
simple. -/
theorem manuscriptSentence266_nontrivial_and_simple :
    Nontrivial H ∧ IsSimpleGroup H :=
  ⟨nontrivial, manuscriptPropositionSimple⟩

/-- **Sentence 267.**  Every homomorphism from the exact group to a countable
MF group is trivial. -/
theorem manuscriptSentence267_homToMF_eq_one
    (M : Type) [Group M] [Countable M] (hM : IsCDEOperatorMF M)
    (f : H →* M) (x : H) :
    f x = 1 := by
  have hfull : manuscriptCoronaMFResidual H = ⊤ := by
    rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
    exact rankTwelve_actualCoronaMFResidual_eq_top
  exact manuscriptFullRadicalKillsMFTargets
    (G := H) (M := M) hfull
    ((isCDEOperatorMF_iff_isOperatorMF M).mp hM) f x

/-- **Sentence 268.**  Applying the preceding radical obstruction to the
identity map rules out MF-ness of the exact group. -/
theorem manuscriptSentence268_not_MF : ¬ IsCDEOperatorMF H :=
  not_isCDEOperatorMF_of_residual_eq_top
    rankTwelve_actualCoronaMFResidual_eq_top

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
