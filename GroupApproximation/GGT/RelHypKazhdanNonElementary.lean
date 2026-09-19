import GroupApproximation.GGT.RelHypFournierFacio
import GroupApproximation.Kazhdan.KazhdanFiniteIndex
import GroupApproximation.Kazhdan.IntegerNotKazhdan

/-!
# An infinite Kazhdan group is not elementary, with no amenability at all

`GGT/RelHypDefinition.lean` derived non-elementarity of the manuscript's `H₀`
from property `(T)` through amenability: an elementary group is amenable, an
amenable Kazhdan group is finite, and `H₀` is infinite.  The first of those
three was the one step this development did not have, and it was carried as the
named `Prop` `ElementaryAmenableStatement`.

**This module deletes that hypothesis**, by replacing the middle of the argument
rather than filling in its first step.  Amenability is not needed at all:

> `C ≤ G` is cyclic of finite index and `G` is infinite, so `C` is infinite, so
> `C ≅ ℤ`.  Property `(T)` passes to finite-index subgroups, so `C` has
> property `(T)`.  But `ℤ` does not.

Every one of those four steps is already a theorem of this repository:

* `Kazhdan/KazhdanFiniteIndex.lean`, `hasKazhdanPropertyT_of_finiteIndex` --
  Bekka--de la Harpe--Valette Theorem 1.7.1, proved here by induction of
  representations through a finite transversal;
* `Kazhdan/Kazhdan.lean`, `HasKazhdanPropertyT.of_mulEquiv`;
* `Kazhdan/IntegerNotKazhdan.lean`, `not_hasKazhdanPropertyT_multiplicative_int`;
* Mathlib's `zmodCyclicMulEquiv`, at `Nat.card = 0`, where `ZMod 0` **is** `ℤ`.

The amenability route is still worth having, and
`GGT/RelHypElementaryAmenable.lean` proves `ElementaryAmenableStatement`
outright as well.  But nothing in the Fournier-Facio chain has to wait for it:
`fournierFacioQuotientStatement_of_osin'` below carries three hypotheses where
`fournierFacioQuotientStatement_of_osin` carried four.

## What the two missing steps of the elementary route were

Worth recording, because the amenability route looks shorter and is not.
"Virtually cyclic implies amenable" needs finite-index permanence of
amenability, and this repository's `Amenability.IsAmenable` is an
invariant-mean definition whose permanence lemmas run through
`hasInvariantMean_of_extension` -- which asks for a **normal** subgroup.  Going
from a finite-index cyclic `C` to a finite-index normal cyclic subgroup means
passing to `C.normalCore` and knowing that a subgroup of a cyclic group is
cyclic.  Neither step is hard, but both are steps, and the `(T)` route has
none of them.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

universe u

/-! ## 1.  A finite-index subgroup of an infinite group is infinite -/

/-- **A finite-index subgroup of an infinite group is infinite.**

The map `(G ⧸ C) × C → G`, `(q, c) ↦ (out q) * c`, is surjective: the chosen
representative of the coset of `g` differs from `g` by an element of `C`.  So a
finite `C` with finitely many cosets would make `G` finite. -/
theorem infinite_subgroup_of_finiteIndex {G : Type u} [Group G] [Infinite G]
    (C : Subgroup G) [C.FiniteIndex] : Infinite ↥C := by
  rw [← not_finite_iff_infinite]
  intro hfinC
  haveI := hfinC
  haveI : Finite (G ⧸ C) := C.finite_quotient_of_finiteIndex
  have hsurj : Function.Surjective
      (fun p : (G ⧸ C) × ↥C => Quotient.out p.1 * (p.2 : G)) := by
    intro g
    have hmem : (Quotient.out (QuotientGroup.mk g : G ⧸ C))⁻¹ * g ∈ C :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g : G ⧸ C))
    refine ⟨⟨QuotientGroup.mk g, ⟨_, hmem⟩⟩, ?_⟩
    show Quotient.out (QuotientGroup.mk g : G ⧸ C) *
      ((Quotient.out (QuotientGroup.mk g : G ⧸ C))⁻¹ * g) = g
    rw [mul_inv_cancel_left]
  haveI : Finite G := Finite.of_surjective _ hsurj
  exact not_finite G

/-! ## 2.  An infinite cyclic group is `ℤ` -/

/-- **An infinite cyclic group is the infinite cyclic group.**

Mathlib's `zmodCyclicMulEquiv` identifies a cyclic group with
`Multiplicative (ZMod (Nat.card α))`, and for an infinite `α` the cardinal is
`0`; `ZMod 0` is `ℤ` by definition, so no transport is needed beyond rewriting
the cardinal. -/
theorem nonempty_mulEquiv_int_of_infinite_isCyclic (A : Type u) [Group A]
    [Infinite A] [IsCyclic A] : Nonempty (Multiplicative ℤ ≃* A) := by
  have hcard : Nat.card A = 0 := Nat.card_eq_zero_of_infinite
  have e := zmodCyclicMulEquiv (inferInstance : IsCyclic A)
  rw [hcard] at e
  exact ⟨e⟩

/-! ## 3.  The theorem, unconditionally -/

/-- **An infinite group with property `(T)` is not elementary.**

Unlike `not_isElementaryGroup_of_infinite_of_kazhdan`, this carries no
hypothesis at all: amenability never appears.  A cyclic subgroup of finite
index in an infinite group is an infinite cyclic group, so it is `ℤ`; property
`(T)` descends to it along Bekka--de la Harpe--Valette; and `ℤ` is not
Kazhdan. -/
theorem not_isElementaryGroup_of_infinite_of_kazhdan' {G : Type} [Group G]
    [Infinite G] (hT : HasKazhdanPropertyT.{0, 0} G) : ¬ IsElementaryGroup G := by
  rintro ⟨C, hfi, hcyc⟩
  haveI := hfi
  haveI := hcyc
  haveI : Infinite ↥C := infinite_subgroup_of_finiteIndex C
  have hTC : HasKazhdanPropertyT.{0, 0} ↥C :=
    GroupApproximation.FiniteIndex.hasKazhdanPropertyT_of_finiteIndex C hT
  obtain ⟨e⟩ := nonempty_mulEquiv_int_of_infinite_isCyclic ↥C
  exact not_hasKazhdanPropertyT_multiplicative_int
    (HasKazhdanPropertyT.of_mulEquiv e hTC)

/-- **The manuscript's `H₀` is non-elementary hyperbolic**, with no named input.
Compare `isNonElementaryHyperbolic_of_kazhdan`, which spends
`ElementaryAmenableStatement`. -/
theorem isNonElementaryHyperbolic_of_kazhdan' {G : Type} [Group G] [Infinite G]
    (hhyp : Hyperbolic.IsHyperbolicGroup G) (hT : HasKazhdanPropertyT.{0, 0} G) :
    IsNonElementaryHyperbolic G :=
  ⟨hhyp, not_isElementaryGroup_of_infinite_of_kazhdan' hT⟩

/-! ## 4.  The Fournier-Facio quotient sentence, on three inputs -/

/-- **`FournierFacioQuotientStatement` from three named `Prop`s.**

The fourth input of `fournierFacioQuotientStatement_of_osin` --
`ElementaryAmenableStatement` -- is gone: non-elementarity of `H₀` is now a
theorem of this development rather than a hypothesis.  What remains is exactly
the literature: Osin's Theorem 2.4, Fournier-Facio's Proposition 2.3, and the
relative hyperbolicity of `(U ∗ H₀, U)`. -/
theorem fournierFacioQuotientStatement_of_osin'
    (hOsin : OsinTheorem24) (hDesign : OsinRelatorDesign)
    (hRelHyp : FreeProductRelativelyHyperbolicStatement) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement := by
  intro H₀ U instH₀ instU hinf hfp htf hhyp hT hUfp hUtf
  exact exists_smallCancellationQuotient hOsin hDesign hRelHyp U H₀ hUfp hUtf
    hinf hfp htf (isNonElementaryHyperbolic_of_kazhdan' hhyp hT)

end RelHyp
end GGT
end GroupApproximation
