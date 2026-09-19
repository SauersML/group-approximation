import GroupApproximation.GGT.RelHypOsinTheorem24
import GroupApproximation.Manuscript.NonMF.FournierFacioInput

/-!
# `FournierFacioQuotientStatement`, discharged to Osin

`Manuscript/NonMF/FournierFacioInput.lean` collects the five citations of the
Fournier-Facio paragraph as fields of `LiteratureInputs`.  The third,
`smallCancellationQuotient : FournierFacioQuotientStatement`, is the sentence

> Small cancellation over the relatively hyperbolic pair `(U ∗ B₀, U)` gives a
> quotient `Δ` of `U ∗ B₀` in which `U` embeds and each generator of `U` equals
> an element of the image of `B₀`; so `Δ` is a finitely presented torsion-free
> quotient of `B₀`

read off `non_mf_groups_exist.tex`.

## What this module does to that field

`fournierFacioQuotientStatement_of_osin` **proves** it, from four named `Prop`s
and nothing else:

* `OsinTheorem24` -- clauses (1) and (5) of Osin's small cancellation theorem,
  which `GGT/RelHypOsinTheorem24.lean` states as the universal closure of the
  two open leaves of `Sofic/OsinWeightedMetric.lean`;
* `OsinRelatorDesign` -- Fournier-Facio's own Proposition 2.3, the choice of
  relators;
* `FreeProductRelativelyHyperbolicStatement` -- that `U ∗ H` is hyperbolic
  relative to `U` when `H` is hyperbolic;
* `ElementaryAmenableStatement` -- that a virtually cyclic group is amenable.

So the citation is not removed -- three of the four inputs are genuinely
Osin's and Fournier-Facio's -- but everything the paragraph does *with* them is
now a theorem: the free product, its finite presentation, its torsion-freeness,
the embedding of `U`, the surjection from `B₀`, and the passage from
"infinite, hyperbolic, Kazhdan" to the non-elementarity Osin's theorem actually
requires.

## Where the property-`(T)` hypothesis is spent

`FournierFacioQuotientStatement` carries `HasKazhdanPropertyT.{0,0} H₀` among
its hypotheses, and the printed sentence quoted above never mentions property
`(T)` -- the paragraph uses it only two sentences later, to conclude that `Δ`
has `(T)`.  It is nevertheless load-bearing *here*, and this module is where
it is spent: Osin's theorem needs `H₀` non-elementary, and
`isNonElementaryHyperbolic_of_kazhdan` is the only route to that from the
remaining hypotheses.

That the hypothesis cannot simply be deleted is proved separately, in
`GGT/RelHypWithoutKazhdan.lean`: at `H₀ = ℤ` -- infinite, finitely presented,
torsion-free, hyperbolic, and elementary -- every quotient is commutative, so
`F₂` embeds in none of them.  `Infinite H₀` is load-bearing for a second and
simpler reason: a finite torsion-free group is trivial, and then `P` is trivial
and contains no `F₂`.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

/-- **`FournierFacioQuotientStatement`, discharged.**

The literature debt of the Fournier-Facio quotient sentence is exactly the four
`Prop`s in the binder list; everything the paragraph asserts on the strength of
them is proved.  Non-elementarity of `H₀` -- which Osin's theorem needs and the
printed sentence does not state -- is derived here from infinitude and property
`(T)`, through the repository's own theorem that an amenable Kazhdan group is
finite. -/
theorem fournierFacioQuotientStatement_of_osin
    (hOsin : OsinTheorem24) (hDesign : OsinRelatorDesign)
    (hRelHyp : FreeProductRelativelyHyperbolicStatement)
    (hEA : ElementaryAmenableStatement) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement := by
  intro H₀ U instH₀ instU hinf hfp htf hhyp hT hUfp hUtf
  exact exists_smallCancellationQuotient hOsin hDesign hRelHyp U H₀ hUfp hUtf
    hinf hfp htf (isNonElementaryHyperbolic_of_kazhdan hEA hhyp hT)

end RelHyp
end GGT
end GroupApproximation
