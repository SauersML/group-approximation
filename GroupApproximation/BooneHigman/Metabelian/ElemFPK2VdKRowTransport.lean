import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKAssemble
import GroupApproximation.Meta.AxiomGuard

/-!
# Van der Kallen's row data by transport along a free `P̃`-set

Lane `bh-met-62`.  This module proves in full a general transport lemma for `VdKRowData`
(module `ElemFPK2VdKAssemble`).

* `vdkRowTransport Ψ : G →* Perm (VdKΩ n R X)`: for any group `G` and bijection
  `Ψ : VdKΩ n R X ≃ G`, it transports the left-regular action of `G` along `Ψ`.
* `vdkRowTransport_eq_of_mul`: if a permutation `σ` satisfies `Ψ (σ w) = g * Ψ w` for all `w`,
  then `σ` is the transport of `g`.
* `VdKRowGroupData n R G`: a homomorphism `act : St_n(R) →* G` and families `col`, `row` of
  elements of `G` that satisfy the five row relator families of `VdKRowData` inside `G`.
* `VdKRowGroupData.toRowData`: if `Ψ` carries `vdkAct` to left multiplication by `act` and
  `vdkCol` to left multiplication by `col`, then left multiplication by `row` gives `VdKRowData`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

/-- Group-side row data: the images of `St_n(R)`, of the column roots and of the row roots in a
group `G`, satisfying the row relator families of `VdKRowData`. -/
structure VdKRowGroupData (n : ℕ) (R : Type*) [Ring R] (G : Type*) [Group G] where
  /-- The image of `St_n(R)`. -/
  act : St n R →* G
  /-- The column roots `x_{i,last}(a)`. -/
  col : Fin n → R → G
  /-- The row roots `x_{last,j}(a)`. -/
  row : Fin n → R → G
  /-- Additivity of the row roots. -/
  row_add : ∀ (j : Fin n) (a b : R), row j a * row j b = row j (a + b)
  /-- Distinct row roots commute. -/
  row_comm : ∀ (j l : Fin n), j ≠ l → ∀ a b : R, row j a * row l b = row l b * row j a
  /-- `x_{last,j}` commutes with `x_{kl}` when `j ≠ k`. -/
  row_act_comm : ∀ (j k l : Fin n) (hkl : k ≠ l), j ≠ k → ∀ a b : R,
    row j a * act (x k l hkl b) = act (x k l hkl b) * row j a
  /-- `⁅x_{last,j}(a), x_{jk}(b)⁆ = x_{last,k}(ab)`. -/
  row_act_commutator : ∀ (j k : Fin n) (hjk : j ≠ k) (a b : R),
    ⁅row j a, act (x j k hjk b)⁆ = row k (a * b)
  /-- `⁅x_{i,last}(a), x_{last,k}(b)⁆ = x_{ik}(ab)` for `i ≠ k`. -/
  col_row_commutator : ∀ (i k : Fin n) (hik : i ≠ k) (a b : R),
    ⁅col i a, row k b⁆ = act (x i k hik (a * b))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowGroupData

variable {R : Type*} [Ring R] {n : ℕ} {X : Type*} {G : Type*} [Group G]

/-- Left multiplication by `g`, transported along `Ψ : VdKΩ n R X ≃ G`. -/
def vdkRowTransportPerm (Ψ : VdKΩ n R X ≃ G) (g : G) : Equiv.Perm (VdKΩ n R X) where
  toFun w := Ψ.symm (g * Ψ w)
  invFun w := Ψ.symm (g⁻¹ * Ψ w)
  left_inv w := by
    simp only [Equiv.apply_symm_apply, inv_mul_cancel_left, Equiv.symm_apply_apply]
  right_inv w := by
    simp only [Equiv.apply_symm_apply, mul_inv_cancel_left, Equiv.symm_apply_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowTransportPerm

theorem vdkRowTransportPerm_apply (Ψ : VdKΩ n R X ≃ G) (g : G) (w : VdKΩ n R X) :
    vdkRowTransportPerm Ψ g w = Ψ.symm (g * Ψ w) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowTransportPerm_apply

/-- The left-regular action of `G`, transported along `Ψ`. -/
def vdkRowTransport (Ψ : VdKΩ n R X ≃ G) : G →* Equiv.Perm (VdKΩ n R X) where
  toFun := vdkRowTransportPerm Ψ
  map_one' := Equiv.ext fun w => by
    simp only [vdkRowTransportPerm_apply, one_mul, Equiv.symm_apply_apply, Equiv.Perm.one_apply]
  map_mul' g h := Equiv.ext fun w => by
    simp only [vdkRowTransportPerm_apply, Equiv.Perm.mul_apply, Equiv.apply_symm_apply,
      mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowTransport

theorem vdkRowTransport_apply (Ψ : VdKΩ n R X ≃ G) (g : G) (w : VdKΩ n R X) :
    vdkRowTransport Ψ g w = Ψ.symm (g * Ψ w) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowTransport_apply

/-- A permutation that `Ψ` intertwines with left multiplication by `g` is the transport of `g`. -/
theorem vdkRowTransport_eq_of_mul (Ψ : VdKΩ n R X ≃ G) (g : G) (σ : Equiv.Perm (VdKΩ n R X))
    (h : ∀ w, Ψ (σ w) = g * Ψ w) : vdkRowTransport Ψ g = σ :=
  Equiv.ext fun w => by rw [vdkRowTransport_apply, ← h, Equiv.symm_apply_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowTransport_eq_of_mul

