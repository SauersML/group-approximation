import GroupApproximation.Computability.AdianRabinGeneral
import GroupApproximation.Sofic.FreeGroupResiduallyFinite
import GroupApproximation.Sofic.HyperlinearReduction
import GroupApproximation.Sofic.SoficTransfer

/-!
# Soficity is a Markov property, so recognising it is undecidable

A third application of `Computability.AdianRabinGeneral`, after operator-MF
and torsion-freeness.  All three Markov clauses for soficity are already
theorems of this repository:

* heredity is `Sofic.isSofic_of_injective`;
* free groups are sofic (`isSofic_freeGroup`), so the collapse side of the
  Rabin variant construction lands in the property;
* the trivial group is sofic, and a finitely presented **nonsofic** group is
  the forbidden example.

The last clause is the only one that is not free, and it is exactly what a
nonsofic-group theorem buys: given one finitely presented nonsofic group,
soficity of a finite presentation is undecidable.  `Covers.TableCover`
manufactures a finitely presented nonsofic group from any finitely generated
one, so the hypothesis of `sofic_recognition_undecidable` is precisely the
existence statement that development already establishes.

Note what is *not* needed: no property of the nonsofic group beyond
nonsoficity, and in particular nothing about how it was built.

## Manuscript status

A consequence of `Computability.AdianRabinGeneral`; certifies no manuscript
step on its own.
-/

namespace GroupApproximation
namespace SoficMarkov

open PresentationCodes AdianRabinGeneral

/-- The trivial group is sofic. -/
theorem isSofic_trivialCode : IsSofic (Carrier trivialCode) := by
  haveI := subsingleton_carrier_trivialCode
  haveI : Finite (Carrier trivialCode) := Finite.of_subsingleton
  exact isSofic_of_residuallyFinite

/-- **Soficity is a Markov property**, given a code for a nonsofic group. -/
noncomputable def soficMarkovData (c : PresentationCode) (hc : ¬ IsSofic (Carrier c)) :
    MarkovData (fun (H : Type) (_ : Group H) ↦ IsSofic H) where
  hereditary f hf hK := isSofic_of_injective f hf hK
  free α _ := isSofic_freeGroup α
  positiveCode := trivialCode
  positive := isSofic_trivialCode
  forbidden := c
  forbidden_not := hc

/-- A finitely presented nonsofic group supplies a nonsofic code. -/
theorem exists_nonsofic_code {H : Type} [Group H]
    [Group.IsFinitelyPresented H] (hH : ¬ IsSofic H) :
    ∃ c : PresentationCode, ¬ IsSofic (Carrier c) := by
  obtain ⟨c, ⟨e⟩⟩ := exists_code_mulEquiv H
  refine ⟨c, fun hc ↦ hH ?_⟩
  exact isSofic_of_injective e.symm.toMonoidHom e.symm.injective hc

/-- **Recognising soficity from a finite presentation is undecidable**, given
one finitely presented nonsofic group and undecidability of the word
problem. -/
theorem sofic_recognition_undecidable {H : Type} [Group H]
    [Group.IsFinitelyPresented H] (hH : ¬ IsSofic H)
    (hw : ¬ ComputablePred AdianRabinWordProblem.wordProblemPred) :
    ¬ ComputablePred
      (codeProperty (fun (K : Type) (_ : Group K) ↦ IsSofic K)) := by
  obtain ⟨c, hc⟩ := exists_nonsofic_code hH
  exact recognition_undecidable_of_wordProblem (soficMarkovData c hc) hw

/-- The nonsofic side is not even recursively enumerable. -/
theorem sofic_negative_side_not_re {H : Type} [Group H]
    [Group.IsFinitelyPresented H] (hH : ¬ IsSofic H)
    (hw : ¬ REPred (fun x ↦ ¬ AdianRabinWordProblem.wordProblemPred x)) :
    ¬ REPred (fun c ↦ ¬ IsSofic (Carrier c)) := by
  obtain ⟨c, hc⟩ := exists_nonsofic_code hH
  exact negative_side_not_re_of_wordProblem (soficMarkovData c hc) hw

end SoficMarkov
end GroupApproximation
