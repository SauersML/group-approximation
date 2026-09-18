import GroupApproximation.Analysis.UniversalCoefficientTheorem
import GroupApproximation.Analysis.CStarExactness
import GroupApproximation.Analysis.ReducedGroupCStarStablyFinite
import GroupApproximation.Manuscript.NinetyNineProblems.StablyFinite
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWCore.QuasidiagonalAlgebra

/-!
# The Related-work sentence on Tikuisis--White--Winter: the statements

Lane TWWCore (work order WO-NM16-2).  This file gives the vocabulary of two
passages of `non_mf_groups_exist.tex`.

* L279--281: "Tikuisis, White, and Winter proved that faithful traces on
  separable nuclear C⋆-algebras satisfying the universal coefficient theorem
  are quasidiagonal."  This is `TikuisisWhiteWinterStatement T`.
* L315--318: Blackadar and Kirchberg "asked whether every separable nuclear
  stably finite C⋆-algebra is quasidiagonal; for algebras that satisfy the
  universal coefficient theorem and have a faithful trace, the theorem of
  Tikuisis, White, and Winter recalled above answers this."  The question is
  `BlackadarKirchbergQuasidiagonalQuestion`.  Its restriction to the UCT
  faithful-trace class is `BlackadarKirchbergQuasidiagonalAnswerUCTFaithfulTrace T`.

The UCT is read at a Kasparov theory `T` as `T.SatisfiesUCT`, i.e.
`KK`-equivalence to a commutative separable algebra (Rosenberg--Schochet).
The endpoints are proved at the concrete Kasparov theory `kasparovKK` in
`Full/TWWCore`.  Nothing here is a hypothesis of any theorem: these are
definitions only.

`stablyFinite_of_mem_answerClass` records that, in the restricted class, the
stable-finiteness clause is automatic: a faithful tracial state forces it.
-/

namespace GroupApproximation.Full.TWWCore

universe u

/-- **The theorem of Tikuisis, White, and Winter**, as a statement about a
Kasparov theory `T` (`non_mf_groups_exist.tex` L279--281): every faithful
tracial state on a separable nuclear C⋆-algebra satisfying the UCT is
quasidiagonal. -/
def TikuisisWhiteWinterStatement (T : KK.KasparovTheory.{u}) : Prop :=
  ∀ S : KK.SepCStarAlgebra.{u}, CStarExactness.IsNuclearCStarAlgebra S →
    T.SatisfiesUCT S → ∀ τ : FaithfulTracialState S,
      Quasidiagonal.IsQuasidiagonalTrace (fun a : S ↦ τ a)

/-- **The Blackadar--Kirchberg question** (`non_mf_groups_exist.tex`
L315--316): is every separable nuclear stably finite C⋆-algebra
quasidiagonal?  It is recorded as a proposition only. -/
def BlackadarKirchbergQuasidiagonalQuestion : Prop :=
  ∀ S : KK.SepCStarAlgebra.{u}, CStarExactness.IsNuclearCStarAlgebra S →
    IsStablyFiniteCStarAlgebra S → IsQuasidiagonalCStarAlgebra S

/-- **The question on the class of L317**: separable nuclear stably finite
C⋆-algebras that satisfy the UCT at `T` and have a faithful tracial state are
quasidiagonal.  This is what the printed sentence says Tikuisis, White, and
Winter answer. -/
def BlackadarKirchbergQuasidiagonalAnswerUCTFaithfulTrace
    (T : KK.KasparovTheory.{u}) : Prop :=
  ∀ S : KK.SepCStarAlgebra.{u}, CStarExactness.IsNuclearCStarAlgebra S →
    IsStablyFiniteCStarAlgebra S → T.SatisfiesUCT S →
      Nonempty (FaithfulTracialState S) → IsQuasidiagonalCStarAlgebra S

/-- In the class of L317 the stable-finiteness clause is automatic: a C⋆-algebra
with a faithful tracial state is stably finite
(`NinetyNineProblems.isStablyFiniteCStarAlgebra_of_faithfulTracialState`). -/
theorem stablyFinite_of_mem_answerClass (S : KK.SepCStarAlgebra.{u})
    (h : Nonempty (FaithfulTracialState S)) : IsStablyFiniteCStarAlgebra S := by
  obtain ⟨τ⟩ := h
  exact NinetyNineProblems.isStablyFiniteCStarAlgebra_of_faithfulTracialState τ

end GroupApproximation.Full.TWWCore
