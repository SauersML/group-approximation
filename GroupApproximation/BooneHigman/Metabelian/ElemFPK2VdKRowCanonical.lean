import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKRowTransport
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.Main
import GroupApproximation.Meta.AxiomGuard

/-!
# The canonical group-side row data and the parabolic map

Lane `bh-met-62`.  Everything here is proved unconditionally, over any ring `R`.

* `vdkRowCanonical n R : VdKRowGroupData n R St_{n+1}(R)`: `act = stab`, `col = colRoot`
  (`x_{i,last}`) and `row = rowRoot` (`x_{last,j}`).  The five row relator families are Steinberg
  relations of `St_{n+1}(R)`.
* `vdkRowPar : R^n × St_n(R) → St_{n+1}(R)`, `(v, g) ↦ (∏ᵢ x_{i,last}(vᵢ)) · stab g`: the
  canonical map `P̃ → St_{n+1}(R)`.
* `vdkRowPar_mul`, `vdkRowPar_inv`, `vdkRowPar_one`: it follows the semidirect product law
  `(v, g)(v', g') = (v + M_g v', g g')`.
* `vdkRowParSubgroup n R`: the image of `vdkRowPar`, as a subgroup of `St_{n+1}(R)`.
* `vdkRowPar_stab`, `vdkRowPar_col`: left multiplication by `stab s` and by `x_{i,last}(a)`
  matches `vdkAct` and `vdkCol` on the parameters.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
  (colRoot rowRoot colVec colVec_add colVec_zero colVec_update_zero rowRoot_add rowRoot_commute
    projectionMatrix stab_conj_colVec)
open scoped commutatorElement Matrix

variable {n : ℕ} {R : Type*} [Ring R]

/-- `x_{last,j}(a)` commutes with `stab x_{kl}(b)` when `j ≠ k`. -/
theorem vdkRow_rowRoot_stab_comm (j k l : Fin n) (hkl : k ≠ l) (hjk : j ≠ k) (a b : R) :
    rowRoot j a * stab n R (x k l hkl b) = stab n R (x k l hkl b) * rowRoot j a := by
  rw [stab_x]
  exact (x_commute_of_ne (Fin.last n) j.castSucc k.castSucc l.castSucc
    (Fin.castSucc_ne_last j).symm (fun h => hkl (Fin.castSucc_inj.mp h))
    (fun h => hjk (Fin.castSucc_inj.mp h)) (Fin.castSucc_ne_last l) a b).eq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRow_rowRoot_stab_comm

/-- `⁅x_{last,j}(a), stab x_{jk}(b)⁆ = x_{last,k}(ab)`. -/
theorem vdkRow_rowRoot_stab_commutator (j k : Fin n) (hjk : j ≠ k) (a b : R) :
    ⁅rowRoot j a, stab n R (x j k hjk b)⁆ = rowRoot k (a * b) := by
  rw [stab_x]
  exact x_commutator (Fin.last n) j.castSucc k.castSucc (Fin.castSucc_ne_last j).symm
    (fun h => hjk (Fin.castSucc_inj.mp h)) (Fin.castSucc_ne_last k).symm a b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRow_rowRoot_stab_commutator

/-- `⁅x_{i,last}(a), x_{last,k}(b)⁆ = stab x_{ik}(ab)` for `i ≠ k`. -/
theorem vdkRow_colRoot_rowRoot_commutator (i k : Fin n) (hik : i ≠ k) (a b : R) :
    ⁅colRoot i a, rowRoot k b⁆ = stab n R (x i k hik (a * b)) := by
  rw [stab_x]
  exact x_commutator i.castSucc (Fin.last n) k.castSucc (Fin.castSucc_ne_last i)
    (Fin.castSucc_ne_last k).symm (fun h => hik (Fin.castSucc_inj.mp h)) a b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRow_colRoot_rowRoot_commutator

variable (n R) in
/-- The canonical group-side row data in `St_{n+1}(R)`. -/
def vdkRowCanonical : VdKRowGroupData n R (St (n + 1) R) where
  act := stab n R
  col := colRoot
  row := rowRoot
  row_add j a b := (rowRoot_add j a b).symm
  row_comm j l _ a b := (rowRoot_commute j l a b).eq
  row_act_comm := vdkRow_rowRoot_stab_comm
  row_act_commutator := vdkRow_rowRoot_stab_commutator
  col_row_commutator := vdkRow_colRoot_rowRoot_commutator

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCanonical

/-- The canonical map `P̃ = R^n ⋊ St_n(R) → St_{n+1}(R)`, `(v, g) ↦ colVec v · stab g`. -/
def vdkRowPar (p : (Fin n → R) × St n R) : St (n + 1) R :=
  colVec p.1 * stab n R p.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowPar

theorem vdkRowPar_apply (v : Fin n → R) (g : St n R) :
    vdkRowPar (v, g) = colVec v * stab n R g :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowPar_apply

theorem vdkRowPar_one : vdkRowPar ((0 : Fin n → R), (1 : St n R)) = 1 := by
  rw [vdkRowPar_apply, colVec_zero, map_one, one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowPar_one

/-- The semidirect product law of the parabolic map. -/
theorem vdkRowPar_mul (v : Fin n → R) (g : St n R) (v' : Fin n → R) (g' : St n R) :
    vdkRowPar (v, g) * vdkRowPar (v', g') = vdkRowPar (v + projectionMatrix g *ᵥ v', g * g') := by
  rw [vdkRowPar_apply, vdkRowPar_apply, vdkRowPar_apply, colVec_add, ← stab_conj_colVec, map_mul]
  simp only [mul_assoc, inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowPar_mul

/-- Inverses in the image of the parabolic map. -/
theorem vdkRowPar_inv (v : Fin n → R) (g : St n R) :
    vdkRowPar (-(projectionMatrix g⁻¹ *ᵥ v), g⁻¹) = (vdkRowPar (v, g))⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [vdkRowPar_mul, neg_add_cancel, inv_mul_cancel, vdkRowPar_one])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowPar_inv

variable (n R) in
/-- The image `P̃` of the parabolic map, a subgroup of `St_{n+1}(R)`. -/
def vdkRowParSubgroup : Subgroup (St (n + 1) R) where
  carrier := Set.range (vdkRowPar (n := n) (R := R))
  mul_mem' := by
    rintro _ _ ⟨⟨v, g⟩, rfl⟩ ⟨⟨v', g'⟩, rfl⟩
    exact ⟨(v + projectionMatrix g *ᵥ v', g * g'), (vdkRowPar_mul v g v' g').symm⟩
  one_mem' := ⟨((0 : Fin n → R), (1 : St n R)), vdkRowPar_one⟩
  inv_mem' := by
    rintro _ ⟨⟨v, g⟩, rfl⟩
    exact ⟨(-(projectionMatrix g⁻¹ *ᵥ v), g⁻¹), vdkRowPar_inv v g⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowParSubgroup

theorem mem_vdkRowParSubgroup (h : St (n + 1) R) :
    h ∈ vdkRowParSubgroup n R ↔ ∃ p : (Fin n → R) × St n R, vdkRowPar p = h :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.mem_vdkRowParSubgroup

/-- Left multiplication by `stab s` on the parameters is `vdkAct`. -/
theorem vdkRowPar_stab (s : St n R) (v : Fin n → R) (g : St n R) :
    vdkRowPar (projectionMatrix s *ᵥ v, s * g) = stab n R s * vdkRowPar (v, g) := by
  rw [vdkRowPar_apply, vdkRowPar_apply, ← stab_conj_colVec, map_mul]
  simp only [mul_assoc, inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowPar_stab

theorem vdkRow_colVec_single (i : Fin n) (a : R) :
    colVec (Pi.single i a : Fin n → R) = colRoot i a :=
  colVec_update_zero i a

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRow_colVec_single

/-- Left multiplication by `x_{i,last}(a)` on the parameters is `vdkCol`. -/
theorem vdkRowPar_col (i : Fin n) (a : R) (v : Fin n → R) (g : St n R) :
    vdkRowPar (v + Pi.single i a, g) = colRoot i a * vdkRowPar (v, g) := by
  rw [vdkRowPar_apply, vdkRowPar_apply, add_comm v, colVec_add, vdkRow_colVec_single, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowPar_col

end GroupApproximation.BooneHigman.Metabelian.ElemFP
