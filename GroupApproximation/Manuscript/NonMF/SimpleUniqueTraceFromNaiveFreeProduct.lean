import GroupApproximation.Manuscript.NonMF.DGO235FromNaiveFreeProduct
import GroupApproximation.Manuscript.NonMF.LoxodromicHypEmbeddedClosureProof

/-!
# Dahmani--Guirardel--Osin, Theorem 2.35, at its own hypothesis

`SimpleUniqueTraceAtHypEmbedded` (`Manuscript/NonMF/OsinTheorem12NonDegenerate`)
states the citation of `cor:regular-nonmf-algebra` at the hypothesis Dahmani,
Guirardel and Osin use: a countable group with a non-degenerate hyperbolically
embedded subgroup and no nontrivial finite normal subgroup.  The torsion-free
assemblies of Section 5 take it as their `hDGO` input.

`DGOTheorem235Printed` states the same citation at acylindrical hyperbolicity.
Osin's Theorem 1.2 in the direction `(AH₄) ⇒ (AH₁)` —
`isAcylindricallyHyperbolic_of_isNonDegenerate_isHypEmbedded`, proved from his
Theorem 5.4 and Lemma 5.12 — turns the first hypothesis into the second, so

* `simpleUniqueTraceAtHypEmbedded_of_dgoTheorem235Printed` derives the
  hypothesis-at-embedding form from the printed form, and
* `simpleUniqueTraceAtHypEmbedded_of_naiveFreeProduct` derives it from Abbott and
  Dahmani's property `P_naive` at acylindrical hyperbolicity, through the closed
  analytic chain of `Manuscript/NonMF/DGO235FromNaiveFreeProduct`.

No further group-theoretic input is needed: the only open statement on this route
is `NaiveFreeProductAtAcylindricallyHyperbolic`.

## Manuscript status

Reduction step for `cor:regular-nonmf-algebra` ("Dahmani, Guirardel, and Osin
give simplicity and uniqueness of the trace"); certifies the sentence once the
geometric Prop has a producer.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.GGT
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.NaiveFreeProduct

/-- **DGO 2.35 at a non-degenerate hyperbolically embedded subgroup, from the
printed form at acylindrical hyperbolicity.**  Osin's `(AH₄) ⇒ (AH₁)` supplies the
acylindrical hyperbolicity. -/
theorem simpleUniqueTraceAtHypEmbedded_of_dgoTheorem235Printed
    (h : DGOTheorem235Printed) : SimpleUniqueTraceAtHypEmbedded := by
  intro G instG instC hemb hrad
  letI := instG
  letI := instC
  obtain ⟨E, hE, hEmb⟩ := hemb
  haveI : IsAcylindricallyHyperbolic G :=
    isAcylindricallyHyperbolic_of_isNonDegenerate_isHypEmbedded hE hEmb
  exact h G hrad

/-- **DGO 2.35 at a non-degenerate hyperbolically embedded subgroup, from
Abbott--Dahmani's `P_naive`.** -/
theorem simpleUniqueTraceAtHypEmbedded_of_naiveFreeProduct
    (h : NaiveFreeProductAtAcylindricallyHyperbolic) : SimpleUniqueTraceAtHypEmbedded :=
  simpleUniqueTraceAtHypEmbedded_of_dgoTheorem235Printed
    (dgoTheorem235Printed_of_naiveFreeProduct h)

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms simpleUniqueTraceAtHypEmbedded_of_dgoTheorem235Printed
#audit_axioms simpleUniqueTraceAtHypEmbedded_of_naiveFreeProduct
