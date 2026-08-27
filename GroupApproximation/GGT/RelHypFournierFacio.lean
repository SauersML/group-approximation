import GroupApproximation.GGT.RelHypOsinTheorem24
import GroupApproximation.Manuscript.NonMF.FournierFacioInput
import GroupApproximation.Algebra.HyperbolicInteger

/-!
# `FournierFacioQuotientStatement`, discharged to Osin, and the exact reason
its property-`(T)` hypothesis cannot be deleted

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
  two open leaves of `Sofic/GreendlingerRelativeTransfer`;
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

## The property-`(T)` hypothesis is load-bearing, and this is proved

`FournierFacioQuotientStatement` carries `HasKazhdanPropertyT.{0,0} H₀` among
its hypotheses.  It is tempting to read that as decoration, since the printed
sentence quoted above never mentions property `(T)` -- the manuscript's `B₀`
happens to have it, and the paragraph uses it only two sentences later, to
conclude that `Δ` has `(T)`.  It is not decoration:
`not_fournierFacioQuotientStatementWithoutKazhdan` proves that the statement
**with that hypothesis deleted is false**, and the counterexample is entirely
in-repo rather than merely arguable.

Take `H₀ = Multiplicative ℤ`.  It is infinite, finitely presented,
torsion-free and hyperbolic -- all four already proved together in
`Algebra/HyperbolicInteger.lean` -- and it is *elementary*, which is precisely
what Osin's theorem forbids.  Take `U = FreeGroup (Fin 2)`, finitely presented
and torsion-free (`Manuscript/NonMF/FreeCommutatorWitness.lean`).  Every
quotient of `Multiplicative ℤ` is commutative, so an injection `U ↪ P` would
force the two free generators to commute, which they do not.

The route by which property `(T)` repairs this is the content of
`GGT/RelHypDefinition.lean`: an infinite group with property `(T)` is not
elementary, because an elementary group is amenable and an amenable Kazhdan
group is finite.  And the counterexample is excluded by exactly that route --
`not_hasKazhdanPropertyT_multiplicative_int` says `ℤ` is not Kazhdan, so the
group that refutes the weakened statement is the first thing the hypothesis
throws out.

`Infinite H₀` is load-bearing for a second, simpler reason: a finite
torsion-free group is trivial, and then `P` is trivial and contains no `F₂`.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

/-! ## 1.  The manuscript's field, proved -/

/-- **`FournierFacioQuotientStatement`, discharged.**

The literature debt of the Fournier-Facio quotient sentence is exactly the four
`Prop`s in the binder list; everything the paragraph asserts on the strength of
them is proved.  Non-elementarity of `H₀` -- which Osin's theorem needs and the
printed sentence does not state -- is derived here from infinitude and property
`(T)`. -/
theorem fournierFacioQuotientStatement_of_osin
    (hOsin : OsinTheorem24) (hDesign : OsinRelatorDesign)
    (hRelHyp : FreeProductRelativelyHyperbolicStatement)
    (hEA : ElementaryAmenableStatement) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement := by
  intro H₀ U instH₀ instU hinf hfp htf hhyp hT hUfp hUtf
  exact exists_smallCancellationQuotient hOsin hDesign hRelHyp U H₀ hUfp hUtf
    hinf hfp htf (isNonElementaryHyperbolic_of_kazhdan hEA hhyp hT)

/-! ## 2.  The property-`(T)` hypothesis is not decoration -/

/-- `FournierFacioQuotientStatement` with the property-`(T)` hypothesis
deleted, and nothing else changed.  Compare
`Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement`. -/
def FournierFacioQuotientStatementWithoutKazhdan : Prop :=
  ∀ (H₀ U : Type) (_ : Group H₀) (_ : Group U),
    Infinite H₀ → Group.IsFinitelyPresented H₀ →
      IsPowerTorsionFree H₀ → Hyperbolic.IsHyperbolicGroup H₀ →
        Group.IsFinitelyPresented U → IsPowerTorsionFree U →
          ∃ (P : Type) (_ : Group P),
            Group.IsFinitelyPresented P ∧ IsPowerTorsionFree P ∧
              (∃ p : H₀ →* P, Function.Surjective p) ∧
              (∃ e : U →* P, Function.Injective e)

/-- **The deleted hypothesis was load-bearing: the weakened statement is
false.**

`H₀ = Multiplicative ℤ` meets every remaining hypothesis, and its quotients are
all commutative, so no free group of rank two embeds in one.  What fails is
non-elementarity, which is what Osin's theorem asks for and what property `(T)`
restores. -/
theorem not_fournierFacioQuotientStatementWithoutKazhdan :
    ¬ FournierFacioQuotientStatementWithoutKazhdan := by
  intro h
  obtain ⟨P, instP, -, -, ⟨p, hp⟩, ⟨e, he⟩⟩ :=
    h (Multiplicative ℤ) Manuscript.NonMF.TheoremC.FreeCommutatorWitness
      inferInstance inferInstance
      Hyperbolic.infinite_multiplicative_int inferInstance
      Hyperbolic.isPowerTorsionFree_multiplicative_int
      Hyperbolic.isHyperbolicGroup_multiplicative_int
      Manuscript.NonMF.TheoremC.freeCommutatorWitness_finitelyPresented
      Manuscript.NonMF.TheoremC.freeCommutatorWitness_torsionFree
  letI := instP
  have hcomm : ∀ x y : P, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := hp x
    obtain ⟨b, rfl⟩ := hp y
    rw [← map_mul p a b, ← map_mul p b a, mul_comm a b]
  apply Manuscript.NonMF.TheoremC.freeWitness_generators_not_commute
  apply he
  rw [map_mul, map_mul]
  exact hcomm _ _

/-- **The counterexample is exactly what the hypothesis throws out.**  The
group refuting the weakened statement is not Kazhdan, so nothing is lost by
keeping the hypothesis; and by
`not_isElementaryGroup_of_infinite_of_kazhdan` the hypothesis buys precisely
the non-elementarity Osin's theorem needs. -/
theorem not_hasKazhdanPropertyT_of_witness :
    ¬ HasKazhdanPropertyT.{0, 0} (Multiplicative ℤ) :=
  not_hasKazhdanPropertyT_multiplicative_int

end RelHyp
end GGT
end GroupApproximation
