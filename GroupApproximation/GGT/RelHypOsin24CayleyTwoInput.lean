import GroupApproximation.GGT.RelHypFreeProductConedFourPoint
import GroupApproximation.GGT.RelHypOsin24CayleyEndpoint

/-!
# The Fournier-Facio quotient sentence on two inputs, and the pair's geometry as
a named object

Every generation of the discharge in `GGT/RelHyp*.lean` has carried three named
`Prop`s: Osin's Theorem 2.4, Fournier-Facio's Proposition 2.3, and the relative
hyperbolicity of `(U ∗ H₀, U)`.  The third is now a theorem --
`GGT/RelHypFreeProductConedFourPoint.freeProductRelativelyHyperbolicStatement_proved`,
off the union-alphabet four-point condition and the discrete peripheral metric
-- so the fourth-generation endpoint runs on two.

The two that remain are the two that are genuinely other people's:

* `OsinTheorem24Cayley` -- clauses (1) and (5) of Osin's small cancellation
  theorem at the relative Cayley graph.  Its Greendlinger half is reduced to a
  single arc bound in `GGT/RelHypOsin24Greendlinger.lean`.
* `OsinRelatorDesignCayley` -- the relator family: one relative generating set,
  and a design at every length demand.

## The relative generating set, named

`OsinRelatorDesignCayley` asks its supplier to *produce* an `X` with
`IsRelHypAt X`, and `isRelativelyHyperbolic_iff_exists_relHypAt` produces one
existentially.  That is enough to typecheck and not enough to build with: the
general-position argument that chooses the `w_k` has to know what the letters
*are*.  `isRelHypAt_freeProductRelGen` names the witness --
`freeProductRelGen U H S hS`, whose alphabet is `X_H ⊔ U` for the finite
symmetric generating set `X_H` of `H` and the whole peripheral factor -- and
certifies it at the explicit constant `max δ 1`.  So the design's obligation is
now a statement about a known alphabet, which is the form Osin's §4 is written
in.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## 1.  The pair's geometry at a named relative generating set -/

/-- **`Γ(U ∗ H, X ⊔ U)` is hyperbolic at `max δ 1`**, in the `ℝ`-valued min form
that `IsRelHypAt` consumes. -/
theorem isHyperbolicSpace_cayley_freeProductRelGen (U H : Type) [Group U]
    [Group H] (S : Finset H) (hS : IsSymmetricGeneratingSet (S : Set H)) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic (S : Set H) δ) :
    IsHyperbolicSpace ((max δ 1 : ℕ) : ℝ)
      (Cayley (freeProductRelGen U H S hS).alphabet) :=
  isHyperbolicSpace_cayley_of_fourPoint _
    (isFourPointHyperbolic_freeProductRelGen U H S hS hδ)

/-- **The relatively hyperbolic structure of `(U ∗ H, U)`, at a named relative
generating set.**

Both clauses of `IsRelHypAt` at the same `X`, which is what the fourth-generation
leaf asks for and what a floating `IsRelativelyHyperbolic` cannot supply without
Osin's independence theorem: hyperbolicity is
`isHyperbolicSpace_cayley_freeProductRelGen`, and the peripheral metric is
discrete by `peripheralMetricLocallyFinite_freeProductRelGen`. -/
theorem isRelHypAt_freeProductRelGen (U H : Type) [Group U] [Group H]
    (S : Finset H) (hS : IsSymmetricGeneratingSet (S : Set H)) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic (S : Set H) δ) :
    IsRelHypAt (G := pairFamily U H) (freeProductRelGen U H S hS) :=
  ⟨((max δ 1 : ℕ) : ℝ),
    isHyperbolicSpace_cayley_freeProductRelGen U H S hS hδ,
    peripheralMetricLocallyFinite_freeProductRelGen U H S hS⟩

/-- **A hyperbolic `H` gives the pair a certified relative generating set.**  The
existential form, with the generating set and the constant of
`IsHyperbolicGroup H` unpacked and spent. -/
theorem exists_isRelHypAt_of_isHyperbolicGroup (U H : Type) [Group U] [Group H]
    (hH : Hyperbolic.IsHyperbolicGroup H) :
    ∃ X : RelativeGeneratingSet (Monoid.CoprodI (pairFamily U H))
        (fun _ : Unit => sourceFactor (pairFamily U H)),
      IsRelHypAt X := by
  obtain ⟨S, hS, δ, hδ⟩ := hH
  exact ⟨freeProductRelGen U H S hS, isRelHypAt_freeProductRelGen U H S hS hδ⟩

/-! ## 2.  The endpoint -/

/-- **`FournierFacioQuotientStatement` from two named `Prop`s.**

`fournierFacioQuotientStatement_of_osin_cayley` with its third hypothesis
discharged.  The property-`(T)` hypothesis of the statement is still spent on
non-elementarity of `H₀`, inside that theorem, through
`isNonElementaryHyperbolic_of_kazhdan'`. -/
theorem fournierFacioQuotientStatement_of_cayley_pair
    (hOsin : OsinTheorem24Cayley) (hDesign : OsinRelatorDesignCayley) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement :=
  fournierFacioQuotientStatement_of_osin_cayley hOsin hDesign
    freeProductRelativelyHyperbolicStatement_proved

end RelHyp
end GGT
end GroupApproximation
