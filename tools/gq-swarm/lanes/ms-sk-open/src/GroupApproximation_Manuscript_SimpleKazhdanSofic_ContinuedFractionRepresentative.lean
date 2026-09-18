import GroupApproximation.Manuscript.SimpleKazhdanSofic.ContinuedFractionCutOracle
import GroupApproximation.Meta.AxiomGuard

/-!
# Every set of naturals has the degree of a continued fraction with digits `1` and `2`

`simple_kazhdan_sofic_group.tex` (origin tip f34e9c0b1), proof of `cor:wp`, second paragraph
(sentence sha256 `a686ac809830`, formerly `7badee43dd9d`):

> Every $D\subseteq\mathbb N$ has the degree of $[0;1+\chi_D(0),1+\chi_D(1),\dots]$, since each
> digit is decided by one strict comparison with a rational computed from earlier digits.

`printedContinuedFractionRepresentative` closes `PrintedContinuedFractionRepresentative`:
* the number and its expansion are skf-degrees' `ContinuedFractionExpansion.tail`,
  `isContinuedFractionOf_tail` and `irrational_tail`;
* `α` computes `S` by one strict comparison per digit
  (`ContinuedFractionOracle.charOracle_turingReducible_slopeOracle`);
* `S` computes `α` by a search over the nested intervals of the convergents
  (`ContinuedFractionOracle.slopeOracle_turingReducible_charOracle`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open ContinuedFractionExpansion ContinuedFractionOracle

open Classical in
theorem printedContinuedFractionRepresentative : PrintedContinuedFractionRepresentative := by
  intro B
  have ha := printedDigits_one_or_two B
  have hS : ∀ k, k ∈ B ↔ (fun k => 1 + if k ∈ B then 1 else 0) k = 2 := by
    intro k
    by_cases h : k ∈ B <;> simp [h]
  exact ⟨tail _ ha 0, isContinuedFractionOf_tail ha, irrational_tail ha 0,
    And.intro (slopeOracle_turingReducible_charOracle ha hS)
      (charOracle_turingReducible_slopeOracle ha hS)⟩

end SimpleKazhdanSofic
end GroupApproximation

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedContinuedFractionRepresentative
