import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Meta.AxiomGuard

/-!
# LEF groups are sofic, and sofic groups are hyperlinear

`simple_kazhdan_sofic_group.tex` at origin/main e80dcf20a, "Finite models", tex l.164–166:

> LEF groups are sofic, and sofic groups are hyperlinear [Pestov, Example 4.5 and Theorem 3.3].

The note uses this citation as a proof step for its main theorem. Both implications are proved in
this repository, so the sentence is stated here as two closed propositions and their conjunction:

* `PrintedLEFGroupsAreSofic`, proved by `isSofic_of_isLEF` (`Sofic/LEFSofic.lean`): the model of an
  LEF group is left multiplication on the finite group `Perm (Fin n)`, with multiplicative defect `0`
  and separation `1`.
* `PrintedSoficGroupsAreHyperlinear`, proved by `isHyperlinear_of_isSofic` (`Sofic/Hyperlinear.lean`):
  `σ ↦ (σ⁻¹).permMatrix ℂ` is a homomorphism, and it doubles the normalized Hamming distance into
  the normalized squared Hilbert–Schmidt distance.

## The definitions against the printed notions

* LEF is defined in the note (tex l.117–119): every finite subset embeds injectively into a finite
  group, preserving all products that stay in that subset. That is `IsTextbookLEF` (`Sofic/LEF.lean`),
  and the statement below uses it. The project's `IsLEF` has a `Perm (Fin n)` target, is normalized
  at `1` and is multiplicative on all pairs of the subset. It is equivalent by `isLEF_iff_textbook`.
* The note does not define sofic or hyperlinear; it defers to Pestov. `IsSofic` is the finitary local
  form: normalized Hamming defect `≤ ε` on pairs of the test set and separation `≥ 1 - ε` on distinct
  pairs. It is equivalent to the product-restricted textbook convention by
  `isSofic_iff_productRestricted` (`Sofic/Sofic.lean`). Pestov's Definition 3.1 is the
  metric-ultraproduct form, and the local form is its standard finitary unwinding.
* `IsHyperlinear` is the finitary local form in the normalized squared Hilbert–Schmidt distance:
  defect `≤ ε` and separation `≥ 2 - ε`, which is `√2` in the Hilbert–Schmidt norm. It is equivalent
  to the product-restricted convention by `isHyperlinear_iff_productRestricted`
  (`Sofic/HyperlinearReduction.lean`).
-/

universe u

namespace GroupApproximation
namespace SimpleKazhdanSofic

/-- tex l.164–166, first clause: LEF groups, in the printed sense of tex l.117–119, are sofic. -/
def PrintedLEFGroupsAreSofic : Prop :=
  ∀ (G : Type u) [Group G], IsTextbookLEF G → IsSofic G

/-- tex l.164–166, first clause, proved by `isSofic_of_isLEF` through `isLEF_iff_textbook`. -/
theorem printedLEFGroupsAreSofic : PrintedLEFGroupsAreSofic.{u} :=
  fun G _ h ↦ isSofic_of_isLEF ((isLEF_iff_textbook G).mpr h)

/-- tex l.164–166, second clause: sofic groups are hyperlinear. -/
def PrintedSoficGroupsAreHyperlinear : Prop :=
  ∀ (G : Type u) [Group G], IsSofic G → IsHyperlinear G

/-- tex l.164–166, second clause, proved by `isHyperlinear_of_isSofic`. -/
theorem printedSoficGroupsAreHyperlinear : PrintedSoficGroupsAreHyperlinear.{u} :=
  fun _ _ h ↦ isHyperlinear_of_isSofic h

/-- tex l.164–166: "LEF groups are sofic, and sofic groups are hyperlinear". -/
def PrintedLEFSoficHyperlinearSentence : Prop :=
  PrintedLEFGroupsAreSofic.{u} ∧ PrintedSoficGroupsAreHyperlinear.{u}

/-- tex l.164–166, the whole sentence. -/
theorem printedLEFSoficHyperlinearSentence : PrintedLEFSoficHyperlinearSentence.{u} :=
  ⟨printedLEFGroupsAreSofic, printedSoficGroupsAreHyperlinear⟩

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedLEFGroupsAreSofic
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedSoficGroupsAreHyperlinear
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedLEFSoficHyperlinearSentence

end SimpleKazhdanSofic
end GroupApproximation
