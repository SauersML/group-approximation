import GroupApproximation.BooneHigman.Metabelian.SuslinMonicPatchEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# A monic twist of `σ` makes `diag(σ, 1)` elementary

Lane `bh-met-93p`.  Let `ρ : A →+* S` and `σ ∈ SL₂(A[X])`.  A **monic witness** for `(ρ, σ)`
(`suslinZHalf_Witness`) consists of
* a ring `B` with `ι : A →+* B`, `j : B →+* S` and `j ∘ ι = ρ`;
* a ring automorphism `φ` of `B[X]`;
* `ε, ε' ∈ SL₂(B[X])` with `diag(ε, 1), diag(ε', 1) ∈ E₃(B[X])`;

such that the twist `τ = φ(ε · σ_B · ε')` (`suslinZHalf_twist`) has two properties.  The
leading coefficient of `τ₀₀` is a unit of `B`, and `diag(τ(0), 1) ∈ E₃(B)`.

**Theorem** (`suslinZHalf_stab_of_witness`).  A monic witness gives `diag(σ_S, 1) ∈ E₃(S[X])`.
The proof runs as follows.
1. The monic Statement `suslinMonicPatch_monicStatement` is proved and holds over every ring.
   It gives `diag(τ, 1) ∈ E₃(B[X])`.
2. Pull back along `φ` (`suslinCongInd_stab_of_map_equiv`).
3. Cancel `ε` and `ε'`.
4. Push forward along `j` (`elementaryGroup_map_le`).

This is the "leading coefficient prime to `p`" route of the lane, in its most permissive form.
The rings `B`, the automorphisms and the multipliers on both sides are all arbitrary.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- The twist `φ(ε · σ_B · ε')` of `σ ∈ GL₂(A[X])` along `ι : A →+* B`. -/
def suslinZHalf_twist {A B : Type*} [CommRing A] [CommRing B] (ι : A →+* B)
    (φ : B[X] ≃+* B[X]) (ε ε' : (Matrix (Fin 2) (Fin 2) B[X])ˣ)
    (σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ) : (Matrix (Fin 2) (Fin 2) B[X])ˣ :=
  elementaryMatrixUnitMap (ι := Fin 2) φ.toRingHom
    (ε * elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.mapRingHom ι) σ * ε')

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZHalf_twist

/-- **A monic witness** for `σ ∈ GL₂(A[X])` over `ρ : A →+* S` (see the module docstring). -/
def suslinZHalf_Witness {A S : Type*} [CommRing A] [CommRing S] (ρ : A →+* S)
    (σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ) : Prop :=
  ∃ (B : Type) (_ : CommRing B) (ι : A →+* B) (j : B →+* S) (_ : j.comp ι = ρ)
    (φ : B[X] ≃+* B[X]) (ε ε' : (Matrix (Fin 2) (Fin 2) B[X])ˣ),
    Matrix.det (ε : Matrix (Fin 2) (Fin 2) B[X]) = 1 ∧
    Matrix.det (ε' : Matrix (Fin 2) (Fin 2) B[X]) = 1 ∧
    stabilizeUnit (R := B[X]) (κ := Unit) ε ∈ elementaryGroup (Fin 2 ⊕ Unit) B[X] ∧
    stabilizeUnit (R := B[X]) (κ := Unit) ε' ∈ elementaryGroup (Fin 2 ⊕ Unit) B[X] ∧
    IsUnit (((suslinZHalf_twist ι φ ε ε' σ : (Matrix (Fin 2) (Fin 2) B[X])ˣ) :
      Matrix (Fin 2) (Fin 2) B[X]) 0 0).leadingCoeff ∧
    stabilizeUnit (R := B) (κ := Unit)
        (elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.constantCoeff (R := B))
          (suslinZHalf_twist ι φ ε ε' σ)) ∈
      elementaryGroup (Fin 2 ⊕ Unit) B

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZHalf_Witness

/-- **The twist reduction**, with the witness data given explicitly. -/
theorem suslinZHalf_stab_of_twist {A S : Type*} {B : Type} [CommRing A] [CommRing B]
    [CommRing S] (ι : A →+* B) (j : B →+* S) (φ : B[X] ≃+* B[X])
    (ε ε' : (Matrix (Fin 2) (Fin 2) B[X])ˣ) (σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ)
    (hdet : Matrix.det (σ : Matrix (Fin 2) (Fin 2) A[X]) = 1)
    (hε : Matrix.det (ε : Matrix (Fin 2) (Fin 2) B[X]) = 1)
    (hε' : Matrix.det (ε' : Matrix (Fin 2) (Fin 2) B[X]) = 1)
    (hsε : stabilizeUnit (R := B[X]) (κ := Unit) ε ∈ elementaryGroup (Fin 2 ⊕ Unit) B[X])
    (hsε' : stabilizeUnit (R := B[X]) (κ := Unit) ε' ∈ elementaryGroup (Fin 2 ⊕ Unit) B[X])
    (hlc : IsUnit (((suslinZHalf_twist ι φ ε ε' σ : (Matrix (Fin 2) (Fin 2) B[X])ˣ) :
      Matrix (Fin 2) (Fin 2) B[X]) 0 0).leadingCoeff)
    (h0 : stabilizeUnit (R := B) (κ := Unit)
        (elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.constantCoeff (R := B))
          (suslinZHalf_twist ι φ ε ε' σ)) ∈
      elementaryGroup (Fin 2 ⊕ Unit) B) :
    stabilizeUnit (R := S[X]) (κ := Unit)
        (elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.mapRingHom (j.comp ι)) σ) ∈
      elementaryGroup (Fin 2 ⊕ Unit) S[X] := by
  have hdetB : Matrix.det ((elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.mapRingHom ι) σ :
      (Matrix (Fin 2) (Fin 2) B[X])ˣ) : Matrix (Fin 2) (Fin 2) B[X]) = 1 := by
    change Matrix.det ((Polynomial.mapRingHom ι).mapMatrix
      (σ : Matrix (Fin 2) (Fin 2) A[X])) = 1
    rw [← RingHom.map_det, hdet, map_one]
  have hρ : Matrix.det ((ε * elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.mapRingHom ι) σ *
      ε' : (Matrix (Fin 2) (Fin 2) B[X])ˣ) : Matrix (Fin 2) (Fin 2) B[X]) = 1 := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hε, hdetB, hε']
    simp only [mul_one]
  have hτ : Matrix.det ((suslinZHalf_twist ι φ ε ε' σ : (Matrix (Fin 2) (Fin 2) B[X])ˣ) :
      Matrix (Fin 2) (Fin 2) B[X]) = 1 := by
    change Matrix.det (φ.toRingHom.mapMatrix
      ((ε * elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.mapRingHom ι) σ * ε' :
        (Matrix (Fin 2) (Fin 2) B[X])ˣ) : Matrix (Fin 2) (Fin 2) B[X])) = 1
    rw [← RingHom.map_det, hρ, map_one]
  have h1 : stabilizeUnit (R := B[X]) (κ := Unit) (suslinZHalf_twist ι φ ε ε' σ) ∈
      elementaryGroup (Fin 2 ⊕ Unit) B[X] :=
    suslinMonicPatch_monicStatement B _ hτ hlc h0
  have h2 : stabilizeUnit (R := B[X]) (κ := Unit)
      (ε * elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.mapRingHom ι) σ * ε') ∈
        elementaryGroup (Fin 2 ⊕ Unit) B[X] :=
    suslinCongInd_stab_of_map_equiv φ _ h1
  have hsplit : elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.mapRingHom ι) σ =
      ε⁻¹ * (ε * elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.mapRingHom ι) σ * ε') *
        ε'⁻¹ := by
    simp only [mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel_left]
  have h3 : stabilizeUnit (R := B[X]) (κ := Unit)
      (elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.mapRingHom ι) σ) ∈
        elementaryGroup (Fin 2 ⊕ Unit) B[X] := by
    rw [hsplit, map_mul, map_mul, map_inv, map_inv]
    exact mul_mem (mul_mem (inv_mem hsε) h2) (inv_mem hsε')
  rw [← Polynomial.mapRingHom_comp, ← suslinLocalGlobal_map_map,
    ← suslinBase3_map_stabilize (κ := Unit)]
  exact elementaryGroup_map_le (Polynomial.mapRingHom j) (Subgroup.mem_map_of_mem _ h3)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZHalf_stab_of_twist

/-- **A monic witness makes `diag(σ_S, 1)` elementary.** -/
theorem suslinZHalf_stab_of_witness {A S : Type*} [CommRing A] [CommRing S] (ρ : A →+* S)
    (σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ)
    (hdet : Matrix.det (σ : Matrix (Fin 2) (Fin 2) A[X]) = 1)
    (hW : suslinZHalf_Witness ρ σ) :
    stabilizeUnit (R := S[X]) (κ := Unit)
        (elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.mapRingHom ρ) σ) ∈
      elementaryGroup (Fin 2 ⊕ Unit) S[X] := by
  obtain ⟨B, _, ι, j, hj, φ, ε, ε', hε, hε', hsε, hsε', hlc, h0⟩ := hW
  rw [← hj]
  exact suslinZHalf_stab_of_twist ι j φ ε ε' σ hdet hε hε' hsε hsε' hlc h0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZHalf_stab_of_witness

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
