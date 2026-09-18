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

namespace VdKRowGroupData

variable (M : VdKRowGroupData n R G) (Ψ : VdKΩ n R X ≃ G)

/-- The transport of `act s` is `vdkAct X s`. -/
theorem transport_act (hact : ∀ (s : St n R) (w : VdKΩ n R X), Ψ (vdkAct X s w) = M.act s * Ψ w)
    (s : St n R) : vdkRowTransport Ψ (M.act s) = vdkAct X s :=
  vdkRowTransport_eq_of_mul Ψ (M.act s) (vdkAct X s) (hact s)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowGroupData.transport_act

/-- The transport of `col i a` is `vdkCol X i a`. -/
theorem transport_col
    (hcol : ∀ (i : Fin n) (a : R) (w : VdKΩ n R X), Ψ (vdkCol X i a w) = M.col i a * Ψ w)
    (i : Fin n) (a : R) : vdkRowTransport Ψ (M.col i a) = vdkCol X i a :=
  vdkRowTransport_eq_of_mul Ψ (M.col i a) (vdkCol X i a) (hcol i a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowGroupData.transport_col

theorem transport_row_add (j : Fin n) (a b : R) :
    vdkRowTransport Ψ (M.row j a) * vdkRowTransport Ψ (M.row j b) =
      vdkRowTransport Ψ (M.row j (a + b)) := by
  rw [← map_mul, M.row_add]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowGroupData.transport_row_add

theorem transport_row_comm (j l : Fin n) (hjl : j ≠ l) (a b : R) :
    vdkRowTransport Ψ (M.row j a) * vdkRowTransport Ψ (M.row l b) =
      vdkRowTransport Ψ (M.row l b) * vdkRowTransport Ψ (M.row j a) := by
  rw [← map_mul, M.row_comm j l hjl a b, map_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowGroupData.transport_row_comm

theorem transport_row_act_comm
    (hact : ∀ (s : St n R) (w : VdKΩ n R X), Ψ (vdkAct X s w) = M.act s * Ψ w)
    (j k l : Fin n) (hkl : k ≠ l) (hjk : j ≠ k) (a b : R) :
    vdkRowTransport Ψ (M.row j a) * vdkAct X (x k l hkl b) =
      vdkAct X (x k l hkl b) * vdkRowTransport Ψ (M.row j a) := by
  rw [← M.transport_act Ψ hact, ← map_mul, M.row_act_comm j k l hkl hjk a b, map_mul]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowGroupData.transport_row_act_comm

theorem transport_row_act_commutator
    (hact : ∀ (s : St n R) (w : VdKΩ n R X), Ψ (vdkAct X s w) = M.act s * Ψ w)
    (j k : Fin n) (hjk : j ≠ k) (a b : R) :
    ⁅vdkRowTransport Ψ (M.row j a), vdkAct X (x j k hjk b)⁆ =
      vdkRowTransport Ψ (M.row k (a * b)) := by
  rw [← M.transport_act Ψ hact, ← map_commutatorElement, M.row_act_commutator j k hjk a b]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowGroupData.transport_row_act_commutator

theorem transport_col_row_commutator
    (hact : ∀ (s : St n R) (w : VdKΩ n R X), Ψ (vdkAct X s w) = M.act s * Ψ w)
    (hcol : ∀ (i : Fin n) (a : R) (w : VdKΩ n R X), Ψ (vdkCol X i a w) = M.col i a * Ψ w)
    (i k : Fin n) (hik : i ≠ k) (a b : R) :
    ⁅vdkCol X i a, vdkRowTransport Ψ (M.row k b)⁆ = vdkAct X (x i k hik (a * b)) := by
  rw [← M.transport_act Ψ hact, ← M.transport_col Ψ hcol, ← map_commutatorElement,
    M.col_row_commutator i k hik a b]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowGroupData.transport_col_row_commutator

/-- **Transport**: group-side row data and a bijection `Ψ : VdKΩ n R X ≃ G` that intertwines
`vdkAct` and `vdkCol` with left multiplication give `VdKRowData n R X`. -/
def toRowData
    (hact : ∀ (s : St n R) (w : VdKΩ n R X), Ψ (vdkAct X s w) = M.act s * Ψ w)
    (hcol : ∀ (i : Fin n) (a : R) (w : VdKΩ n R X), Ψ (vdkCol X i a w) = M.col i a * Ψ w) :
    VdKRowData n R X where
  Trow j a := vdkRowTransport Ψ (M.row j a)
  row_add := M.transport_row_add Ψ
  row_comm := M.transport_row_comm Ψ
  row_act_comm := M.transport_row_act_comm Ψ hact
  row_act_commutator := M.transport_row_act_commutator Ψ hact
  col_row_commutator := M.transport_col_row_commutator Ψ hact hcol

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowGroupData.toRowData

end VdKRowGroupData

end GroupApproximation.BooneHigman.Metabelian.ElemFP
