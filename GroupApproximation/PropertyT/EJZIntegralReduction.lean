import GroupApproximation.PropertyT.FinitelyGeneratedRingPermanence
import GroupApproximation.Steinberg.FreeRingPresentation
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Kazhdan.Kazhdan
import GroupApproximation.Meta.AxiomGuard

/-!
# Reduction of the full elementary property-(T) theorem to integral free rings

The prime-characteristic proof does not by itself cover rings of
characteristic `p ^ k`: property `(T)` passes from a group to its quotients,
not from a quotient back to the source.  There is nevertheless no separate
coefficient-characteristic obstruction in the *full* theorem.  Every
finitely generated unital ring is a quotient of `FreeAlgebra ℤ X` for a
finite type `X`.  The induced map of elementary groups is surjective, so
property `(T)` for the integral free source descends to the given ring.

This file formalizes precisely that reduction.  It does not assume a
literature theorem and does not claim the still-missing integral source
statement: that statement occurs explicitly as the antecedent of the proved
implication.
-/

namespace GroupApproximation

/-- Property `(T)` in every elementary rank over every finite-rank free
associative `ℤ`-algebra.  This is the characteristic-zero universal case to
which the general coefficient theorem reduces. -/
def FreeIntegralGeneralRankElementaryPropertyT : Prop :=
  ∀ (X : Type) [Fintype X] (n : ℕ), 3 ≤ n →
    HasKazhdanPropertyT.{0, 0}
      (elementaryGroup (Fin n) (FreeAlgebra ℤ X))

/-- The coefficient-general Ershov--Jaikin-Zapirain conclusion, stated with
the manuscript's literal finite-generation hypothesis. -/
def FinitelyGeneratedRingGeneralRankElementaryPropertyT : Prop :=
  ∀ (A : Type) [Ring A], IsFinitelyGeneratedRing A →
    ∀ (n : ℕ), 3 ≤ n →
      HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) A)

/-- **The full coefficient theorem reduces to the integral free case.**

The proof chooses the finite free `ℤ`-algebra presentation of the
coefficient ring, maps elementary matrices coefficientwise, proves that this
group map is surjective, and descends property `(T)` through that quotient.
No characteristic hypothesis occurs. -/
theorem freeIntegralGeneralRank_implies_finitelyGeneratedRingGeneralRank
    (hfree : FreeIntegralGeneralRankElementaryPropertyT) :
    FinitelyGeneratedRingGeneralRankElementaryPropertyT := by
  intro A _ hfg n hn
  haveI : Algebra.FiniteType ℤ A :=
    (isFinitelyGeneratedRing_iff_finiteType_int A).mp hfg
  obtain ⟨X, hX, f, hf⟩ := exists_finite_freeAlgebraInt_ringHom_surjection A
  letI : Fintype X := hX
  exact HasKazhdanPropertyT.of_surjective
    (elementaryGroupMap (ι := Fin n) f)
    (elementaryGroupMap_surjective_of_surjective f hf)
    (hfree X n hn)

/-- Closed, binder-free form of the integral reduction. -/
def PrintedEJZIntegralReduction : Prop :=
  FreeIntegralGeneralRankElementaryPropertyT →
    FinitelyGeneratedRingGeneralRankElementaryPropertyT

theorem printedEJZIntegralReduction : PrintedEJZIntegralReduction :=
  freeIntegralGeneralRank_implies_finitelyGeneratedRingGeneralRank

#audit_closed_axioms printedEJZIntegralReduction

end GroupApproximation
