import GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeWord
import GroupApproximation.BooneHigman.Metabelian.ChainHost
import GroupApproximation.Meta.AxiomGuard

/-!
# The affine elementary host acts self-similarly (lane bh-met-02)

Research node `positive-char-polynomial-affine-groups-are-self-similar-proof`, step 4.  The affine
elementary group `R^n ⋊ E_n(R)` of lane bh-met-08 (`Chain.AffineElementaryGroup`), over
`R = F[s_σ]`, acts on the tree over the letters `F^n × F^{σ ∖ i₀}` by `act`.

Main declarations:
* `affMat x`, `affVec x`: the matrix and vector parts, with the product law `affVec_mul`;
* `treeRep i₀`: the tree representation `R^n ⋊ E_n(R) →* Aut(T)`;
* `stateElem i₀ x e a`: the element `(carry, σ_a(g))` of the host;
* `state_treeRep`: the state of `treeRep x` at the letter `(e, a)` is `treeRep (stateElem x e a)`;
* `isSelfSimilar_treeRep`: the range of `treeRep i₀` is self-similar.
-/

noncomputable section

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharPHost
namespace TreeHost

open MvPolynomial
open scoped Matrix

variable {F : Type} [Field F] {σ : Type} [DecidableEq σ] (i₀ : σ) {n : ℕ}

/-- The matrix part of an element of `R^n ⋊ E_n(R)`. -/
def affMat (x : Chain.AffineElementaryGroup n (MvPolynomial σ F)) :
    Matrix (Fin n) (Fin n) (MvPolynomial σ F) :=
  ((x.right : (Matrix (Fin n) (Fin n) (MvPolynomial σ F))ˣ) :
    Matrix (Fin n) (Fin n) (MvPolynomial σ F))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.affMat

/-- The vector part of an element of `R^n ⋊ E_n(R)`. -/
def affVec (x : Chain.AffineElementaryGroup n (MvPolynomial σ F)) : Fin n → MvPolynomial σ F :=
  Multiplicative.toAdd x.left

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.affVec

theorem affMat_mul (x y : Chain.AffineElementaryGroup n (MvPolynomial σ F)) :
    affMat (x * y) = affMat x * affMat y :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.affMat_mul

theorem affVec_mul (x y : Chain.AffineElementaryGroup n (MvPolynomial σ F)) :
    affVec (x * y) = affVec x + affMat x *ᵥ affVec y :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.affVec_mul

theorem affMat_one : affMat (1 : Chain.AffineElementaryGroup n (MvPolynomial σ F)) = 1 :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.affMat_one

theorem affVec_one : affVec (1 : Chain.AffineElementaryGroup n (MvPolynomial σ F)) = 0 :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.affVec_one

/-- An element of `R^n ⋊ E_n(R)` as a permutation of words. -/
def affPerm (x : Chain.AffineElementaryGroup n (MvPolynomial σ F)) :
    Equiv.Perm (List (Letter (Fin n) F i₀)) where
  toFun := act i₀ (affMat x) (affVec x)
  invFun := act i₀ (affMat x⁻¹) (affVec x⁻¹)
  left_inv w := by
    show act i₀ (affMat x⁻¹) (affVec x⁻¹) (act i₀ (affMat x) (affVec x) w) = w
    rw [act_act, ← affMat_mul, ← affVec_mul, inv_mul_cancel, affMat_one, affVec_one, act_one]
  right_inv w := by
    show act i₀ (affMat x) (affVec x) (act i₀ (affMat x⁻¹) (affVec x⁻¹) w) = w
    rw [act_act, ← affMat_mul, ← affVec_mul, mul_inv_cancel, affMat_one, affVec_one, act_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.affPerm

variable (n) in
/-- **The tree representation** of `R^n ⋊ E_n(R)`, `R = F[s_σ]`, on the tree over
`F^n × F^{σ ∖ i₀}`. -/
def treeRep :
    Chain.AffineElementaryGroup n (MvPolynomial σ F) →* Trees.TreeAut (Letter (Fin n) F i₀) where
  toFun x := ⟨affPerm i₀ x, isTreeMap_act i₀ (affMat x) (affVec x)⟩
  map_one' := Trees.TreeAut.ext fun w => by
    show act i₀ (affMat (1 : Chain.AffineElementaryGroup n (MvPolynomial σ F)))
      (affVec (1 : Chain.AffineElementaryGroup n (MvPolynomial σ F))) w = w
    rw [affMat_one, affVec_one, act_one]
  map_mul' x y := Trees.TreeAut.ext fun w => by
    show act i₀ (affMat (x * y)) (affVec (x * y)) w =
      act i₀ (affMat x) (affVec x) (act i₀ (affMat y) (affVec y) w)
    rw [act_act, affMat_mul, affVec_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.treeRep

theorem treeRep_smul (x : Chain.AffineElementaryGroup n (MvPolynomial σ F))
    (w : List (Letter (Fin n) F i₀)) : treeRep i₀ n x • w = act i₀ (affMat x) (affVec x) w :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.treeRep_smul

/-- The state of `(b, g)` at the letter `(e, a)`: the pair `(carry, σ_a(g))`. -/
def stateElem (x : Chain.AffineElementaryGroup n (MvPolynomial σ F)) (e : Fin n → F)
    (a : {i : σ // i ≠ i₀} → F) : Chain.AffineElementaryGroup n (MvPolynomial σ F) :=
  ⟨Multiplicative.ofAdd (carry i₀ (affMat x) (affVec x) (e, a)),
    elementaryGroupMap (shift i₀ a) x.right⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.stateElem

/-- **States of the tree representation** stay in its range. -/
theorem state_treeRep (x : Chain.AffineElementaryGroup n (MvPolynomial σ F)) (e : Fin n → F)
    (a : {i : σ // i ≠ i₀} → F) :
    Trees.TreeAut.state (treeRep i₀ n x) [(e, a)] = treeRep i₀ n (stateElem i₀ x e a) := by
  refine Trees.TreeAut.ext fun v => Trees.TreeAut.state_smul_eq_of_smul_append _ ?_
  show act i₀ (affMat x) (affVec x) ((e, a) :: v) =
    act i₀ (affMat x) (affVec x) [(e, a)] ++
      act i₀ (affMat (stateElem i₀ x e a)) (affVec (stateElem i₀ x e a)) v
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.state_treeRep

/-- **Self-similarity**: the range of the tree representation is self-similar. -/
theorem isSelfSimilar_treeRep : Trees.IsSelfSimilar (treeRep (F := F) i₀ n).range :=
  (Trees.isSelfSimilar_range_iff _).2 fun x y =>
    ⟨stateElem i₀ x y.1 y.2, state_treeRep i₀ x y.1 y.2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.isSelfSimilar_treeRep

end TreeHost
end CharPHost
end Metabelian
end BooneHigman
end GroupApproximation

end
