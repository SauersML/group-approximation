import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.BigOperators.Pi
import GroupApproximation.Leavitt.ElementaryRoots
import GroupApproximation.Meta.AxiomGuard

/-!
# The affine elementary group `R^I ⋊ E_I(R)` (lane bh-met-05)

Research node `affine-extension-of-fp-elementary-group-is-fp`.  We define the action
`affAction` of `E_I(R)` on the column vectors `R^I` (written multiplicatively), the semidirect
product `AffineElementary I R = R^I ⋊ E_I(R)`, and prove the relations (C1)–(C3) of the
affine presentation in it, writing `τ k = inl (e_k)`:

* `model_c1`: `x_{ij}(ε)` commutes with `τ k` for `k ≠ j`;
* `model_c2`: `x_{ij}(1) τ_j x_{ij}(1)⁻¹ = τ_j τ_i`;
* `model_c3`: the `τ k` commute;
* `model_commutator`: `⁅x_{ik}(r), τ_k⁆ = inl (r e_i)`;
* `vec_hom_ext`: homomorphisms out of `R^I` agree once they agree on the `r e_i`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace AffineFP

open scoped Matrix commutatorElement

section Defs

variable (I R : Type*) [Fintype I] [DecidableEq I] [CommRing R]

/-- The automorphism of `R^I` given by an invertible matrix. -/
def vecEquiv (g : (Matrix I I R)ˣ) : Multiplicative (I → R) ≃* Multiplicative (I → R) where
  toFun v := Multiplicative.ofAdd ((g : Matrix I I R) *ᵥ Multiplicative.toAdd v)
  invFun v :=
    Multiplicative.ofAdd (((g⁻¹ : (Matrix I I R)ˣ) : Matrix I I R) *ᵥ Multiplicative.toAdd v)
  left_inv v := by
    change Multiplicative.ofAdd (((g⁻¹ : (Matrix I I R)ˣ) : Matrix I I R) *ᵥ
      ((g : Matrix I I R) *ᵥ Multiplicative.toAdd v)) = v
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, ofAdd_toAdd]
  right_inv v := by
    change Multiplicative.ofAdd ((g : Matrix I I R) *ᵥ
      (((g⁻¹ : (Matrix I I R)ˣ) : Matrix I I R) *ᵥ Multiplicative.toAdd v)) = v
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, ofAdd_toAdd]
  map_mul' v w :=
    congrArg Multiplicative.ofAdd
      (Matrix.mulVec_add (g : Matrix I I R) (Multiplicative.toAdd v) (Multiplicative.toAdd w))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.vecEquiv

/-- Invertible matrices act on `R^I`. -/
def vecAction : (Matrix I I R)ˣ →* MulAut (Multiplicative (I → R)) where
  toFun := vecEquiv I R
  map_one' := by
    refine MulEquiv.ext fun v => ?_
    change Multiplicative.ofAdd (((1 : (Matrix I I R)ˣ) : Matrix I I R) *ᵥ
      Multiplicative.toAdd v) = v
    rw [Units.val_one, Matrix.one_mulVec, ofAdd_toAdd]
  map_mul' g h := by
    refine MulEquiv.ext fun v => ?_
    change Multiplicative.ofAdd (((g * h : (Matrix I I R)ˣ) : Matrix I I R) *ᵥ
      Multiplicative.toAdd v) =
      Multiplicative.ofAdd ((g : Matrix I I R) *ᵥ ((h : Matrix I I R) *ᵥ Multiplicative.toAdd v))
    rw [Units.val_mul, Matrix.mulVec_mulVec]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.vecAction

/-- The action of the elementary group `E_I(R)` on `R^I`. -/
def affAction : elementaryGroup I R →* MulAut (Multiplicative (I → R)) :=
  (vecAction I R).comp (elementaryGroup I R).subtype

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.affAction

/-- The affine elementary group `R^I ⋊ E_I(R)`. -/
abbrev AffineElementary : Type _ :=
  SemidirectProduct (Multiplicative (I → R)) (elementaryGroup I R) (affAction I R)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineElementary

end Defs

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

theorem elementaryUnit_mulVec (i j : I) (h : i ≠ j) (a : R) (v : I → R) :
    (elementaryUnit i j h a : Matrix I I R) *ᵥ v = v + Pi.single i (a * v j) := by
  have e : (elementaryUnit i j h a : Matrix I I R) = 1 + Matrix.single i j a := rfl
  rw [e, Matrix.add_mulVec, Matrix.one_mulVec]
  exact congrArg (fun w => v + w) (Matrix.single_mulVec i j a v)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.elementaryUnit_mulVec

theorem affAction_root (i j : I) (h : i ≠ j) (a : R) (u : I → R) :
    affAction I R (elementaryRoot i j h a) (Multiplicative.ofAdd u) =
      Multiplicative.ofAdd (u + Pi.single i (a * u j)) := by
  change Multiplicative.ofAdd ((elementaryUnit i j h a : Matrix I I R) *ᵥ u) = _
  rw [elementaryUnit_mulVec]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.affAction_root

/-- The vectors `r e_i` generate `R^I`. -/
theorem closure_single_eq_top :
    Subgroup.closure (Set.range fun p : I × R =>
      Multiplicative.ofAdd (Pi.single p.1 p.2 : I → R)) = ⊤ := by
  apply top_unique
  intro v _
  have e : ∏ i, Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd v i) : I → R) = v := by
    rw [← ofAdd_sum, Finset.univ_sum_single, ofAdd_toAdd]
  rw [← e]
  exact Subgroup.prod_mem _ fun i _ => Subgroup.subset_closure ⟨(i, Multiplicative.toAdd v i), rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.closure_single_eq_top

theorem vec_hom_ext {M : Type*} [Group M] {f g : Multiplicative (I → R) →* M}
    (h : ∀ (i : I) (r : R), f (Multiplicative.ofAdd (Pi.single i r)) =
      g (Multiplicative.ofAdd (Pi.single i r))) : f = g := by
  refine MonoidHom.eq_of_eqOn_dense closure_single_eq_top ?_
  rintro _ ⟨p, rfl⟩
  exact h p.1 p.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.vec_hom_ext

/-- Conjugating a basis translation by an elementary root. -/
theorem model_conj_single (i j : I) (h : i ≠ j) (a : R) (k : I) (r : R) :
    (SemidirectProduct.inr (elementaryRoot i j h a) : AffineElementary I R) *
      SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single k r : I → R)) *
      (SemidirectProduct.inr (elementaryRoot i j h a))⁻¹ =
    SemidirectProduct.inl
      (Multiplicative.ofAdd (Pi.single k r + Pi.single i (a * Pi.single k r j) : I → R)) := by
  rw [← map_inv, ← SemidirectProduct.inl_aut, affAction_root]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.model_conj_single

theorem model_c1 (i j : I) (h : i ≠ j) (ε : R) (k : I) (hk : k ≠ j) :
    Commute (SemidirectProduct.inr (elementaryRoot i j h ε) : AffineElementary I R)
      (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single k (1 : R) : I → R))) := by
  have e := model_conj_single i j h ε k 1
  rw [Pi.single_eq_of_ne hk.symm, mul_zero, Pi.single_zero, add_zero] at e
  exact mul_inv_eq_iff_eq_mul.mp e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.model_c1
