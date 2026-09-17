import GroupApproximation.Manuscript.NonMFNotes.Full.FixedRadicalMembership.Retraction
import GroupApproximation.Manuscript.NonMFNotes.Full.RadicalArithmetic.Arithmetic
import GroupApproximation.Meta.AxiomGuard

/-!
# The fixed-group radical theorem at the radical-word predicate

Manuscript `non_mf_group_notes.tex`, `thm:fixed-radical-membership`:

> "There is a finitely presented non-MF group `U` for which membership in
> `Res_MF(U)` is undecidable."

The radical-word predicate of `thm:mf-radical-arithmetic` is
`GroupApproximation.Full.NN02.RadicalWordCode`.  Its fibre over a code is, by
definition, the predicate `RadicalWordAt` of
`FixedRadicalMembership.Retraction` (`radicalWordCode_iff`), so the generic
theorem proved there is restated here in exactly the shape of the fixed-group
statement.

The input group -- a finitely presented MF group with undecidable word problem
(Kharlampovich's solvable group, MF by Tikuisis--White--Winter) -- is not in the
repository.  `notesFixedRadicalMembership_of_mfFactor` therefore takes the two
concrete properties of an input code `c` as hypotheses; it is not the closed
theorem, and no closed form is stated.
-/

namespace GroupApproximation.Full.NN03

open PresentationCodes AdianRabinWordProblem

/-- The radical-word predicate of `thm:mf-radical-arithmetic`, at a fixed code,
is `RadicalWordAt`. -/
theorem radicalWordCode_iff (c : PresentationCode) (v : List (ℕ × Bool)) :
    GroupApproximation.Full.NN02.RadicalWordCode (c, v) ↔ RadicalWordAt c v :=
  Iff.rfl

/-- **`thm:fixed-radical-membership`, from an MF input with undecidable word
problem.**  For every presentation code `c` whose group is MF and has
undecidable word problem, the finitely presented free product `U = A*E`
(`fixedRadicalCode c`) is non-MF and radical membership in `U` is undecidable.
The hypotheses are properties of `c`; producing such a `c` is the
Kharlampovich + Tikuisis--White--Winter input of the printed proof. -/
theorem notesFixedRadicalMembership_of_mfFactor (c : PresentationCode)
    (hMF : IsOperatorMF (Carrier c)) (hWP : ¬ ComputablePred (WordProblem c)) :
    ∃ u : PresentationCode, ¬ IsOperatorMF (Carrier u) ∧
      ¬ ComputablePred fun v : List (ℕ × Bool) ↦
        GroupApproximation.Full.NN02.RadicalWordCode (u, v) :=
  ⟨fixedRadicalCode c, (fixedRadicalCode_fp_not_isOperatorMF c).2,
    radicalMembership_undecidable_of_mfFactor c hMF hWP⟩

#audit_axioms GroupApproximation.Full.NN03.radicalWordCode_iff
#audit_axioms GroupApproximation.Full.NN03.notesFixedRadicalMembership_of_mfFactor

end GroupApproximation.Full.NN03
