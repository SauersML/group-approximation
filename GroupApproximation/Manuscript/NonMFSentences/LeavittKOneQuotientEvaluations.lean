import GroupApproximation.Manuscript.NonMFSentences.LeavittKOneFormulaSentences
import GroupApproximation.KOne.LeavittKOneScalarQuotient
import GroupApproximation.Meta.AxiomGuard

/-!
# The two evaluations after `cor:leavitt-mf-quotient`, at the printed quotient

`non_mf_groups_exist.tex`, tex 1320–1322:

> For `d=2` the quotient is trivial for every countable field `k`, so every homomorphism from
> `L_k(1,2)^×` to an MF group is trivial.  For `k=𝔽_q` the quotient is cyclic of order
> `gcd(q-1,d-1)`.

"The quotient" is the one the corollary computes, `H/EL_d(R) ≅ K_1(R) ≅ k^×/(k^×)^{d-1}` for
`R = L_k(1,d)` and `H = R^×`, and it is the largest MF quotient `H/Rad_MF(H)` of the
introduction (tex 247).  `KOne/LeavittKOneScalarQuotient.lean` evaluates the answer group
`k^×/(k^×)^{d-1}`, and `LeavittKOneFormulaSentences` identifies both printed quotients with it.
This module composes the two, so both sentences are statements about `L_k(1,d)`.

* `manuscriptSentence_quotientTrivialRankTwo` --- at `d = 2`, `GL_2(R)/EL_2(R)` and
  `H/Rad_MF(H)` are trivial, **so** every homomorphism from `L_k(1,2)^×` to an MF group is
  trivial: every element of `H` has trivial class in `H/Rad_MF(H)`, so it lies in the
  intersection of the kernels of all homomorphisms to MF groups.
* `manuscriptSentence_quotientCyclicFiniteField` --- at a finite field with `q` elements, both
  quotients are cyclic of order `gcd(q-1,d-1)`.
-/

namespace GroupApproximation
namespace LeavittKOneQuotientEvaluations

open AryLeavitt AlgebraicK Manuscript.OneSidedMFRadical MFQuotientUnits

/-! ### `d = 2` -/

/-- **tex 1320**, as printed.

> For `d=2` the quotient is trivial for every countable field `k`, so every homomorphism from
> `L_k(1,2)^×` to an MF group is trivial.

The quotient is trivial at both of its printed spellings, `GL_2(R)/EL_2(R)` and
`H/Rad_MF(H)`, and the consequence is stated for `H = L_k(1,2)^×`. -/
def PrintedLeavittQuotientTrivialRankTwo : Prop :=
  ∀ (k : Type) [Field k] [Countable k],
    (letI : (elementaryGroup (Fin 2) (AryLeavittAlgebra k 2)).Normal :=
        LeavittMFQuotientSentences.elementaryGroup_normal k 2 le_rfl;
      Subsingleton ((Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k 2))ˣ ⧸
        elementaryGroup (Fin 2) (AryLeavittAlgebra k 2))) ∧
      Subsingleton ((AryLeavittAlgebra k 2)ˣ ⧸ mfHomKernel (AryLeavittAlgebra k 2)ˣ) ∧
      ∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ (f : (AryLeavittAlgebra k 2)ˣ →* M) (x : (AryLeavittAlgebra k 2)ˣ), f x = 1

/-- **Closed endpoint: tex 1320.** -/
theorem manuscriptSentence_quotientTrivialRankTwo : PrintedLeavittQuotientTrivialRankTwo := by
  intro k _ _
  letI : (elementaryGroup (Fin 2) (AryLeavittAlgebra k 2)).Normal :=
    LeavittMFQuotientSentences.elementaryGroup_normal k 2 le_rfl
  haveI : Subsingleton (kˣ ⧸ LeavittKOneFormula.unitPowSubgroup k (2 - 1)) :=
    LeavittScalarQuotient.manuscriptSentence_leavittScalarQuotientRankTwo k 2 rfl
  have hEL := LeavittKOneFormulaSentences.manuscriptSentence_quotientByElementaryIsScalarQuotient
    k 2 le_rfl
  have hRad := LeavittKOneFormulaSentences.manuscriptSentence_unitGroupQuotient k 2 le_rfl
  have hsub : Subsingleton ((AryLeavittAlgebra k 2)ˣ ⧸ mfHomKernel (AryLeavittAlgebra k 2)ˣ) :=
    hRad.some.toEquiv.subsingleton
  refine ⟨hEL.some.toEquiv.subsingleton, hsub, ?_⟩
  intro M _ hM f x
  have hx : x ∈ mfHomKernel (AryLeavittAlgebra k 2)ˣ :=
    (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  exact (mem_mfHomKernel_iff x).mp hx M hM f

/-! ### Finite fields -/

/-- **tex 1322**, as printed.

> For `k=𝔽_q` the quotient is cyclic of order `gcd(q-1,d-1)`.

At every finite field, with `q` read as `Nat.card k`, and every `d ≥ 2`, at both printed
spellings of the quotient. -/
def PrintedLeavittQuotientCyclicFiniteField : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (d : ℕ) (hd : 2 ≤ d),
    (letI : (elementaryGroup (Fin d) (AryLeavittAlgebra k d)).Normal :=
        LeavittMFQuotientSentences.elementaryGroup_normal k d hd;
      IsCyclic ((Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ ⧸
          elementaryGroup (Fin d) (AryLeavittAlgebra k d)) ∧
        Nat.card ((Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ ⧸
          elementaryGroup (Fin d) (AryLeavittAlgebra k d)) = Nat.gcd (Nat.card k - 1) (d - 1)) ∧
      IsCyclic ((AryLeavittAlgebra k d)ˣ ⧸ mfHomKernel (AryLeavittAlgebra k d)ˣ) ∧
        Nat.card ((AryLeavittAlgebra k d)ˣ ⧸ mfHomKernel (AryLeavittAlgebra k d)ˣ)
          = Nat.gcd (Nat.card k - 1) (d - 1)

/-- **Closed endpoint: tex 1322.** -/
theorem manuscriptSentence_quotientCyclicFiniteField : PrintedLeavittQuotientCyclicFiniteField := by
  intro k _ _ d hd
  letI : (elementaryGroup (Fin d) (AryLeavittAlgebra k d)).Normal :=
    LeavittMFQuotientSentences.elementaryGroup_normal k d hd
  have hQ : IsCyclic (kˣ ⧸ LeavittKOneFormula.unitPowSubgroup k (d - 1)) ∧
      Nat.card (kˣ ⧸ LeavittKOneFormula.unitPowSubgroup k (d - 1))
        = Nat.gcd (Nat.card k - 1) (d - 1) :=
    LeavittScalarQuotient.manuscriptSentence_leavittScalarQuotientFiniteField k d hd
  haveI := hQ.1
  have hEL := LeavittKOneFormulaSentences.manuscriptSentence_quotientByElementaryIsScalarQuotient
    k d hd
  have hRad := LeavittKOneFormulaSentences.manuscriptSentence_unitGroupQuotient k d hd
  refine ⟨⟨isCyclic_of_surjective hEL.some.symm hEL.some.symm.surjective, ?_⟩,
    isCyclic_of_surjective hRad.some.symm hRad.some.symm.surjective, ?_⟩
  · rw [← hQ.2]
    exact Nat.card_congr hEL.some.toEquiv
  · rw [← hQ.2]
    exact Nat.card_congr hRad.some.toEquiv

end LeavittKOneQuotientEvaluations
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms
  GroupApproximation.LeavittKOneQuotientEvaluations.manuscriptSentence_quotientTrivialRankTwo
#audit_closed_axioms
  GroupApproximation.LeavittKOneQuotientEvaluations.manuscriptSentence_quotientCyclicFiniteField
