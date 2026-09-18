import GroupApproximation.BooneHigman.Metabelian.SuslinMonicPatchEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# A monic elementary twist of `σ` makes `diag(σ, 1)` elementary

Lane `bh-met-93p`.  Let `A` be a commutative ring and `σ ∈ SL₂(A[X])`.  An **elementary monic
witness** for `σ` (`suslinZHalf_Witness`) consists of
* a ring automorphism `φ` of `A[X]`, and
* two elementary matrices `ε, ε' ∈ E₂(A[X])`,

such that the leading coefficient of `τ₀₀` is a unit of `A`, where `τ = φ(ε σ ε')` is the twist
(`suslinZHalf_twist`).  The witness is a concrete algebraic condition on `σ`.  It never mentions
`E₃`, localizations, or the conclusion.

**Theorem** (`suslinZHalf_stab_of_witness`).  Assume `SL₃(A) = E₃(A)`.  This is the family
hypothesis at level `k`, NOT at level `k + 1`.  Then an elementary monic witness gives
`diag(σ, 1) ∈ E₃(A[X])` GLOBALLY.  The proof runs as follows.
1. `det τ = 1`, and `diag(τ(0), 1) ∈ E₃(A)` holds by `SL₃(A) = E₃(A)`
   (`suslinBase3Fam_stab_mem`).
2. The monic Statement `suslinMonicPatch_monicStatement` is proved and holds over every ring.
   It gives `diag(τ, 1) ∈ E₃(A[X])`.
3. Pull back along `φ` (`suslinCongInd_stab_of_map_equiv`).
4. Cancel `ε` and `ε'`, whose stabilizations are elementary by `elementaryStabilization`.

This is the lane's "make the leading coefficient prime to `p` after an automorphism and
elementary moves" route, in its natural global form.  The companion module
`SuslinZHalfEndpoint.lean` records the Cohn counterexample.  It shows that one-sided witnesses
do NOT always exist, so this route alone cannot close the target.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- The twist `φ(ε σ ε')` of `σ ∈ GL₂(A[X])`. -/
noncomputable def suslinZHalf_twist {A : Type*} [CommRing A] (φ : A[X] ≃+* A[X])
    (ε ε' σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ) : (Matrix (Fin 2) (Fin 2) A[X])ˣ :=
  elementaryMatrixUnitMap (ι := Fin 2) φ.toRingHom (ε * σ * ε')

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZHalf_twist

/-- **An elementary monic witness** for `σ ∈ GL₂(A[X])`: an automorphism `φ` of `A[X]` and
`ε, ε' ∈ E₂(A[X])` such that `φ(ε σ ε')₀₀` has unit leading coefficient. -/
def suslinZHalf_Witness {A : Type*} [CommRing A] (σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ) : Prop :=
  ∃ φ : A[X] ≃+* A[X], ∃ ε ∈ elementaryGroup (Fin 2) A[X], ∃ ε' ∈ elementaryGroup (Fin 2) A[X],
    IsUnit (((suslinZHalf_twist φ ε ε' σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ) :
      Matrix (Fin 2) (Fin 2) A[X]) 0 0).leadingCoeff

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZHalf_Witness

/-- **An elementary monic witness makes `diag(σ, 1)` elementary** over `A[X]`, given
`SL₃(A) = E₃(A)`. -/
theorem suslinZHalf_stab_of_witness {A : Type} [CommRing A]
    (hSL : SpecialLinearInElementary A 3) (σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ)
    (hdet : Matrix.det (σ : Matrix (Fin 2) (Fin 2) A[X]) = 1)
    (hW : suslinZHalf_Witness σ) :
    stabilizeUnit (R := A[X]) (κ := Unit) σ ∈ elementaryGroup (Fin 2 ⊕ Unit) A[X] := by
  obtain ⟨φ, ε, hε, ε', hε', hlc⟩ := hW
  have hρ : Matrix.det ((ε * σ * ε' : (Matrix (Fin 2) (Fin 2) A[X])ˣ) :
      Matrix (Fin 2) (Fin 2) A[X]) = 1 := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
      suslin_det_eq_one_of_mem_elementaryGroup hε, hdet,
      suslin_det_eq_one_of_mem_elementaryGroup hε']
    simp only [mul_one]
  have hτ : Matrix.det ((suslinZHalf_twist φ ε ε' σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ) :
      Matrix (Fin 2) (Fin 2) A[X]) = 1 := by
    change Matrix.det (φ.toRingHom.mapMatrix
      ((ε * σ * ε' : (Matrix (Fin 2) (Fin 2) A[X])ˣ) : Matrix (Fin 2) (Fin 2) A[X])) = 1
    rw [← RingHom.map_det, hρ, map_one]
  have hc : Matrix.det ((elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.constantCoeff (R := A))
      (suslinZHalf_twist φ ε ε' σ) : (Matrix (Fin 2) (Fin 2) A)ˣ) :
        Matrix (Fin 2) (Fin 2) A) = 1 := by
    change Matrix.det ((Polynomial.constantCoeff (R := A)).mapMatrix
      ((suslinZHalf_twist φ ε ε' σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ) :
        Matrix (Fin 2) (Fin 2) A[X])) = 1
    rw [← RingHom.map_det, hτ, map_one]
  have h1 : stabilizeUnit (R := A[X]) (κ := Unit) (suslinZHalf_twist φ ε ε' σ) ∈
      elementaryGroup (Fin 2 ⊕ Unit) A[X] :=
    suslinMonicPatch_monicStatement A _ hτ hlc (suslinBase3Fam_stab_mem (n := 2) hSL _ hc)
  have h2 : stabilizeUnit (R := A[X]) (κ := Unit) (ε * σ * ε') ∈
      elementaryGroup (Fin 2 ⊕ Unit) A[X] :=
    suslinCongInd_stab_of_map_equiv φ _ h1
  have hi : stabilizeUnit (R := A[X]) (κ := Unit) ε⁻¹ ∈ elementaryGroup (Fin 2 ⊕ Unit) A[X] :=
    (elementaryStabilization (ι := Fin 2) (κ := Unit) (R := A[X]) ⟨ε⁻¹, inv_mem hε⟩).2
  have hi' : stabilizeUnit (R := A[X]) (κ := Unit) ε'⁻¹ ∈ elementaryGroup (Fin 2 ⊕ Unit) A[X] :=
    (elementaryStabilization (ι := Fin 2) (κ := Unit) (R := A[X]) ⟨ε'⁻¹, inv_mem hε'⟩).2
  have hsplit : σ = ε⁻¹ * (ε * σ * ε') * ε'⁻¹ := by
    simp only [mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel_left]
  rw [hsplit, map_mul, map_mul]
  exact mul_mem (mul_mem hi h2) hi'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZHalf_stab_of_witness

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
