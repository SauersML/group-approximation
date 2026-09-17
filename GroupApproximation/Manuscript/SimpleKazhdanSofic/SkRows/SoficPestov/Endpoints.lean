import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SoficPestov.FromSofic
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SoficPestov.ToSofic
import GroupApproximation.Sofic.LEFSofic

/-!
# Pestov, Example 4.5, in the printed normalization

tex l.345: "It is LEF, so it is sofic~\cite[Example~4.5]{Pestov} [...]"

* `isSofic_iff_isSoficPestov`: corpus `IsSofic` (defect `≤ ε`, pairwise separation `≥ 1 - ε`,
  arbitrary finite models) is equivalent to Pestov's normalization (`Sym(n)`, `φ 1 = 1`,
  defect `< ε`, nontrivial elements at distance `> 1 - ε` from `1`).
* `isSoficPestov_iff_isSoficPestovRestricted`: testing all pairs or only product-closed pairs
  gives the same notion.
* `manuscriptSentence_pestovExampleFourFive`: LEF groups are sofic in Pestov's normalization,
  composing `isSofic_of_isLEF` with the equivalence.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SkRows
namespace SoficPestov

/-- **Corpus soficity is soficity in Pestov's printed normalization.** -/
theorem isSofic_iff_isSoficPestov (G : Type*) [Group G] : IsSofic G ↔ IsSoficPestov G :=
  ⟨isSoficPestov_of_isSofic, fun h =>
    isSofic_of_isSoficPestovRestricted (isSoficPestovRestricted_of_isSoficPestov h)⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SoficPestov.isSofic_iff_isSoficPestov

/-- Pestov's two conventions for the test set (all pairs, or only product-closed pairs) agree. -/
theorem isSoficPestov_iff_isSoficPestovRestricted (G : Type*) [Group G] :
    IsSoficPestov G ↔ IsSoficPestovRestricted G :=
  ⟨isSoficPestovRestricted_of_isSoficPestov, fun h =>
    isSoficPestov_of_isSofic (isSofic_of_isSoficPestovRestricted h)⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SoficPestov.isSoficPestov_iff_isSoficPestovRestricted

/-- **tex l.345, [Example 4.5]{Pestov}.**  An LEF group is sofic in Pestov's printed
normalization. -/
theorem manuscriptSentence_pestovExampleFourFive {G : Type*} [Group G] (h : IsLEF G) :
    IsSoficPestov G :=
  isSoficPestov_of_isSofic (isSofic_of_isLEF h)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SoficPestov.manuscriptSentence_pestovExampleFourFive

/-- The same endpoint from the textbook form of LEF (`isLEF_iff_textbook`). -/
theorem manuscriptSentence_pestovExampleFourFive_textbook {G : Type*} [Group G]
    (h : IsTextbookLEF G) : IsSoficPestov G :=
  manuscriptSentence_pestovExampleFourFive ((isLEF_iff_textbook G).mpr h)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SoficPestov.manuscriptSentence_pestovExampleFourFive_textbook

end SoficPestov
end SkRows
end SimpleKazhdanSofic
end GroupApproximation
