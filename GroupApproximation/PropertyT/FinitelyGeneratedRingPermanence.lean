import GroupApproximation.PropertyT.FinitelyGeneratedRing
import GroupApproximation.Meta.AxiomGuard

/-!
# Quotient permanence of finite generation for coefficient rings

The coefficient hypothesis in the Ershov--Jaikin-Zapirain statement is
generation as a unital ring.  A surjective unital ring homomorphism carries
finite generation to the target.  This is the coefficient-ring step used when
the property-`(T)` theorem descends from a finite-rank free integral algebra to
an arbitrary finitely generated ring.

The proof uses the already established equivalence with
`Algebra.FiniteType ℤ`.  It does not assert property `(T)` and does not
reverse quotient permanence for property `(T)`.
-/

namespace GroupApproximation

variable {A B : Type*} [Ring A] [Ring B]

/-- A quotient of a finitely generated unital ring is finitely generated. -/
theorem IsFinitelyGeneratedRing.of_surjective
    (hA : IsFinitelyGeneratedRing A) (f : A →+* B)
    (hf : Function.Surjective f) : IsFinitelyGeneratedRing B := by
  rw [isFinitelyGeneratedRing_iff_finiteType_int] at hA ⊢
  letI : Algebra.FiniteType ℤ A := hA
  exact Algebra.FiniteType.of_surjective f.toIntAlgHom hf

/-! The closed statement audited below records exactly the quotient
permanence used by the integral reduction. -/

def PrintedFinitelyGeneratedRingQuotientPermanence : Prop :=
  ∀ (A B : Type) [Ring A] [Ring B], IsFinitelyGeneratedRing A →
    ∀ f : A →+* B, Function.Surjective f → IsFinitelyGeneratedRing B

theorem printedFinitelyGeneratedRingQuotientPermanence :
    PrintedFinitelyGeneratedRingQuotientPermanence := by
  intro A B _ _ hA f hf
  exact hA.of_surjective f hf

#audit_closed_axioms printedFinitelyGeneratedRingQuotientPermanence

end GroupApproximation
