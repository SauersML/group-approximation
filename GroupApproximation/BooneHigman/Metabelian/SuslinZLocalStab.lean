import GroupApproximation.BooneHigman.Metabelian.SuslinZLocalGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Transvection monic witnesses make `diag(σ, 1)` elementary

Lane `bh-met-93u`.  Let `τ = φ(ε σ ε')` be the twist with `ε, ε' ∈ G(A[X])`
(`suslinZLocal_Group`).
* `det τ = 1` when `det σ = 1` (`suslinZLocal_twist_det`).
* `diag(τ, 1) ∈ E₃(A[X])` implies `diag(σ, 1) ∈ E₃(A[X])` (`suslinZLocal_stab_of_twist`).  Pull
  back along `φ` and cancel `ε, ε'`, whose stabilizations are elementary by
  `suslinZLocal_stab_mem`.
* **Global** (`suslinZLocal_stab_of_globalWitness`): `SL₃(A) = E₃(A)` and a witness give
  `diag(σ, 1) ∈ E₃(A[X])`, via the proved monic Statement `suslinMonicPatch_monicStatement`.
* **Local** (`suslinZLocal_stab_of_localWitness`): over a local ring `B`, a witness gives
  `diag(σ, 1) ∈ E₃(B[X])` unconditionally, via `suslinMonicLocal_good`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- The twist of a determinant-one matrix by transvection multipliers has determinant one. -/
theorem suslinZLocal_twist_det {A : Type*} [CommRing A] (φ : A[X] ≃+* A[X])
    {ε ε' σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ} (hε : ε ∈ suslinZLocal_Group A[X])
    (hε' : ε' ∈ suslinZLocal_Group A[X])
    (hdet : Matrix.det (σ : Matrix (Fin 2) (Fin 2) A[X]) = 1) :
    Matrix.det ((suslinZHalf_twist φ ε ε' σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ) :
      Matrix (Fin 2) (Fin 2) A[X]) = 1 := by
  have hρ : Matrix.det ((ε * σ * ε' : (Matrix (Fin 2) (Fin 2) A[X])ˣ) :
      Matrix (Fin 2) (Fin 2) A[X]) = 1 := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
      suslinZLocal_det_eq_one hε, hdet, suslinZLocal_det_eq_one hε']
    simp only [mul_one]
  change Matrix.det (φ.toRingHom.mapMatrix
    ((ε * σ * ε' : (Matrix (Fin 2) (Fin 2) A[X])ˣ) : Matrix (Fin 2) (Fin 2) A[X])) = 1
  rw [← RingHom.map_det, hρ, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZLocal_twist_det

/-- If the twist `φ(ε σ ε')` is stably elementary, so is `σ`. -/
theorem suslinZLocal_stab_of_twist {A : Type*} [CommRing A] (φ : A[X] ≃+* A[X])
    {ε ε' σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ} (hε : ε ∈ suslinZLocal_Group A[X])
    (hε' : ε' ∈ suslinZLocal_Group A[X])
    (h : stabilizeUnit (R := A[X]) (κ := Unit) (suslinZHalf_twist φ ε ε' σ) ∈
      elementaryGroup (Fin 2 ⊕ Unit) A[X]) :
    stabilizeUnit (R := A[X]) (κ := Unit) σ ∈ elementaryGroup (Fin 2 ⊕ Unit) A[X] := by
  have h2 : stabilizeUnit (R := A[X]) (κ := Unit) (ε * σ * ε') ∈
      elementaryGroup (Fin 2 ⊕ Unit) A[X] :=
    suslinCongInd_stab_of_map_equiv φ _ h
  have hsplit : σ = ε⁻¹ * (ε * σ * ε') * ε'⁻¹ := by
    simp only [mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel_left]
  rw [hsplit, map_mul, map_mul]
  exact mul_mem (mul_mem (suslinZLocal_stab_mem (inv_mem hε)) h2)
    (suslinZLocal_stab_mem (inv_mem hε'))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZLocal_stab_of_twist

/-- **Global.**  With `SL₃(A) = E₃(A)`, a transvection monic witness for `σ ∈ SL₂(A[X])` gives
`diag(σ, 1) ∈ E₃(A[X])`. -/
theorem suslinZLocal_stab_of_globalWitness {A : Type} [CommRing A]
    (hSL : SpecialLinearInElementary A 3) (σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ)
    (hdet : Matrix.det (σ : Matrix (Fin 2) (Fin 2) A[X]) = 1)
    (hW : suslinZLocal_Witness σ) :
    stabilizeUnit (R := A[X]) (κ := Unit) σ ∈ elementaryGroup (Fin 2 ⊕ Unit) A[X] := by
  obtain ⟨φ, ε, hε, ε', hε', hlc⟩ := hW
  have hτ := suslinZLocal_twist_det φ hε hε' hdet
  have hc : Matrix.det ((elementaryMatrixUnitMap (ι := Fin 2)
      (Polynomial.constantCoeff (R := A)) (suslinZHalf_twist φ ε ε' σ) :
        (Matrix (Fin 2) (Fin 2) A)ˣ) : Matrix (Fin 2) (Fin 2) A) = 1 := by
    change Matrix.det ((Polynomial.constantCoeff (R := A)).mapMatrix
      ((suslinZHalf_twist φ ε ε' σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ) :
        Matrix (Fin 2) (Fin 2) A[X])) = 1
    rw [← RingHom.map_det, hτ, map_one]
  exact suslinZLocal_stab_of_twist φ hε hε'
    (suslinMonicPatch_monicStatement A _ hτ hlc (suslinBase3Fam_stab_mem (n := 2) hSL _ hc))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZLocal_stab_of_globalWitness

/-- **Local.**  Over a local ring `B`, a transvection monic witness for `σ ∈ SL₂(B[X])` gives
`diag(σ, 1) ∈ E₃(B[X])`, with no hypothesis on `SL₃(B)`. -/
theorem suslinZLocal_stab_of_localWitness {B : Type*} [CommRing B] [IsLocalRing B]
    (σ : (Matrix (Fin 2) (Fin 2) B[X])ˣ)
    (hdet : Matrix.det (σ : Matrix (Fin 2) (Fin 2) B[X]) = 1)
    (hW : suslinZLocal_Witness σ) :
    stabilizeUnit (R := B[X]) (κ := Unit) σ ∈ elementaryGroup (Fin 2 ⊕ Unit) B[X] := by
  obtain ⟨φ, ε, hε, ε', hε', hlc⟩ := hW
  exact suslinZLocal_stab_of_twist φ hε hε'
    (suslinMonicLocal_good _ _ _ hlc le_rfl _ (suslinZLocal_twist_det φ hε hε' hdet) rfl rfl)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZLocal_stab_of_localWitness

/-- The image of a determinant-one matrix under a ring map has determinant one. -/
theorem suslinZLocal_det_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (σ : (Matrix (Fin 2) (Fin 2) R)ˣ) (hdet : Matrix.det (σ : Matrix (Fin 2) (Fin 2) R) = 1) :
    Matrix.det ((elementaryMatrixUnitMap (ι := Fin 2) f σ : (Matrix (Fin 2) (Fin 2) S)ˣ) :
      Matrix (Fin 2) (Fin 2) S) = 1 := by
  change Matrix.det (f.mapMatrix (σ : Matrix (Fin 2) (Fin 2) R)) = 1
  rw [← RingHom.map_det, hdet, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZLocal_det_map

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
