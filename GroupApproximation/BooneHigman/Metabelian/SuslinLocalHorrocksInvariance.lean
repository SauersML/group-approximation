import GroupApproximation.BooneHigman.Metabelian.SuslinLocalGlobalPatching
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin local-global route, part 5: invariance of the Quillen set

Lane `bh-met-60`.  For `τ ∈ GL_N(A[X])` the Quillen set
`Q(τ) = {a : τ(X + aY) τ(X)⁻¹ ∈ E_N(A[X][Y])}` (`SuslinLocalGlobalQuillen`,
`SuslinLocalGlobalQuillen.lean`) is invariant under

* **left multiplication by elementary matrices** `ε ∈ E_N(A[X])`:
  `(ετ)(X + aY) (ετ)(X)⁻¹ = ε(X + aY) · [τ(X + aY) τ(X)⁻¹] · ε(X)⁻¹`, and both outer factors
  are elementary over `A[X][Y]` (images of `ε` under ring homomorphisms).  No normality of
  `E_N` is needed, since the conjugation is by an element of `E_N` itself;
* **right multiplication by constant matrices** `C(g)`, `g ∈ GL_N(A)`: the substitution
  `X ↦ X + aY` fixes `A`, so `C(g)` cancels and the Quillen matrix is unchanged.

These are the freedoms used by the local Horrocks reduction (elementary row operations on the
left, constant corrections on the right), and they let the isolated local Statement of
`SuslinLocalHorrocksStatement.lean` produce its Quillen element for *some* matrix
`ε τ C(g)` rather than for `τ` itself.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable {A : Type*} [CommRing A] {N : ℕ}

/-- The substitution `X ↦ X + aY` fixes the constants `A`. -/
theorem suslinLocalHorrocks_shift_comp_C (a : A) :
    (suslinLocalGlobalShift a).comp (Polynomial.C : A →+* Polynomial A) =
      (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)).comp
        (Polynomial.C : A →+* Polynomial A) :=
  RingHom.ext fun x ↦ suslinLocalGlobalShift_C a x

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalHorrocks_shift_comp_C

/-- Right multiplication by a constant matrix does not change the Quillen matrix
`τ(X + aY) τ(X)⁻¹`. -/
theorem suslinLocalHorrocks_quillenMatrix_mul_C
    (τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    (g : Matrix.GeneralLinearGroup (Fin N) A) (a : A) :
    elementaryMatrixUnitMap (ι := Fin N) (suslinLocalGlobalShift a)
        (τ * elementaryMatrixUnitMap (ι := Fin N) (Polynomial.C (R := A)) g) *
      (elementaryMatrixUnitMap (ι := Fin N)
        (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A))
        (τ * elementaryMatrixUnitMap (ι := Fin N) (Polynomial.C (R := A)) g))⁻¹ =
    elementaryMatrixUnitMap (ι := Fin N) (suslinLocalGlobalShift a) τ *
      (elementaryMatrixUnitMap (ι := Fin N)
        (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)) τ)⁻¹ := by
  rw [map_mul, map_mul, suslinLocalGlobal_map_map, suslinLocalGlobal_map_map,
    suslinLocalHorrocks_shift_comp_C, mul_inv_rev]
  simp only [mul_assoc, mul_inv_cancel_left]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalHorrocks_quillenMatrix_mul_C

/-- `Q(τ C(g)) = Q(τ)` for a constant matrix `g ∈ GL_N(A)`. -/
theorem suslinLocalHorrocks_quillen_mul_C_iff
    (τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    (g : Matrix.GeneralLinearGroup (Fin N) A) (a : A) :
    SuslinLocalGlobalQuillen
        (τ * elementaryMatrixUnitMap (ι := Fin N) (Polynomial.C (R := A)) g) a ↔
      SuslinLocalGlobalQuillen τ a := by
  unfold SuslinLocalGlobalQuillen
  rw [suslinLocalHorrocks_quillenMatrix_mul_C]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalHorrocks_quillen_mul_C_iff

/-- `Q(τ) ⊆ Q(ε τ)` for an elementary matrix `ε ∈ E_N(A[X])`. -/
theorem suslinLocalHorrocks_quillen_elementary_mul
    {τ ε : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)}
    (hε : ε ∈ elementaryGroup (Fin N) (Polynomial A)) {a : A}
    (ha : SuslinLocalGlobalQuillen τ a) : SuslinLocalGlobalQuillen (ε * τ) a := by
  unfold SuslinLocalGlobalQuillen at ha ⊢
  have hsh := elementaryGroup_map_le (ι := Fin N) (suslinLocalGlobalShift a)
    (Subgroup.mem_map_of_mem _ hε)
  have hC := elementaryGroup_map_le (ι := Fin N)
    (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)) (Subgroup.mem_map_of_mem _ hε)
  have h := mul_mem (mul_mem hsh ha) (inv_mem hC)
  rw [map_mul, map_mul, mul_inv_rev]
  simpa only [mul_assoc] using h

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalHorrocks_quillen_elementary_mul

/-- `Q(ε τ C(g)) = Q(τ)` for `ε ∈ E_N(A[X])` and `g ∈ GL_N(A)`: the backward inclusion. -/
theorem suslinLocalHorrocks_quillen_of_elementary_mul_C
    {τ ε : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)}
    (hε : ε ∈ elementaryGroup (Fin N) (Polynomial A))
    (g : Matrix.GeneralLinearGroup (Fin N) A) {a : A}
    (ha : SuslinLocalGlobalQuillen
      (ε * τ * elementaryMatrixUnitMap (ι := Fin N) (Polynomial.C (R := A)) g) a) :
    SuslinLocalGlobalQuillen τ a := by
  have h₁ : SuslinLocalGlobalQuillen (ε * τ) a :=
    (suslinLocalHorrocks_quillen_mul_C_iff (ε * τ) g a).1 ha
  have h₂ := suslinLocalHorrocks_quillen_elementary_mul (inv_mem hε) h₁
  rwa [inv_mul_cancel_left] at h₂

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalHorrocks_quillen_of_elementary_mul_C

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
