import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.OfCorpus
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.ToCorpus
import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Meta.AxiomGuard

/-!
# Elek–Szabó Theorem 2 in the printed normalization, tex 345–348

`simple_kazhdan_sofic_group.tex`, l.345–348:

> It is LEF, so it is sofic~\cite[Example~4.5]{Pestov} and
> hyperlinear~\cite[Theorem~2]{ElekSzabo}, and $L(G)$ embeds in $\mathcal R^\omega$ ...

Elek–Szabó, Math. Ann. 332 (2005), Theorem 2: sofic groups are hyperlinear, where hyperlinear
means `IsHyperlinearElekSzabo` (unitaries `U(n)`, `‖A‖₂ = (tr(A* A)/n)^{1/2}`, constant `√2`).

Proof route.

* `isHyperlinear_iff_elekSzabo`: the printed notion is equivalent to the corpus `IsHyperlinear`
  (`OfCorpus.lean`, `ToCorpus.lean`).
* `manuscriptSentence_elekSzaboTheoremTwo`: `IsSofic G → IsHyperlinearElekSzabo G`, composing the
  corpus `isHyperlinear_of_isSofic` with the equivalence.
* `isHyperlinearElekSzabo_of_isLEF`: the tex chain LEF ⇒ sofic ⇒ hyperlinear, via
  `isSofic_of_isLEF`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SkRows
namespace HyperlinearElekSzabo

/-- The printed Elek–Szabó normalization of hyperlinearity agrees with the corpus one. -/
theorem isHyperlinear_iff_elekSzabo {G : Type*} [Group G] :
    IsHyperlinear G ↔ IsHyperlinearElekSzabo G :=
  ⟨isHyperlinearElekSzabo_of_isHyperlinear, isHyperlinear_of_isHyperlinearElekSzabo⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.isHyperlinear_iff_elekSzabo

/-- Elek–Szabó, Theorem 2, as cited at tex 345–348: sofic groups are hyperlinear in the printed
normalization. -/
theorem manuscriptSentence_elekSzaboTheoremTwo {G : Type*} [Group G] (hS : IsSofic G) :
    IsHyperlinearElekSzabo G :=
  isHyperlinearElekSzabo_of_isHyperlinear (isHyperlinear_of_isSofic hS)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.manuscriptSentence_elekSzaboTheoremTwo

/-- The tex chain: an LEF group is hyperlinear in the printed normalization. -/
theorem isHyperlinearElekSzabo_of_isLEF {G : Type*} [Group G] (hL : IsLEF G) :
    IsHyperlinearElekSzabo G :=
  manuscriptSentence_elekSzaboTheoremTwo (isSofic_of_isLEF hL)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.isHyperlinearElekSzabo_of_isLEF

end HyperlinearElekSzabo
end SkRows
end SimpleKazhdanSofic
end GroupApproximation
