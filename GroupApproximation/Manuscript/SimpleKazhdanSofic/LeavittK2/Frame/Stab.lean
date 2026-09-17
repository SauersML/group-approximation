import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Frame.VertexComplex
import Mathlib.GroupTheory.GroupAction.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Base stabilizers `J`, `K`, the swap `τ` and the automorphism `η` of `K`

Lane `sk-leavitt-07` (carto `sk-leavitt`).  Khanh (arXiv:2609.08428v1), proof of Theorem 5.1:
`J = Stab(v_0)`, `K = Stab(v_0, v_1)`, `τ` exchanges `v_0 ↔ v_1`, and `η k = τ k τ⁻¹`.

Last-index convention (lane 05): the base vertex of `A^{m+1}` is `e_last`, and the base edge of
`A^{m+2}` is `(e_last, e_{cs last})`, where `cs = Fin.castSucc`.

* `frameVertexStab A m`: the stabilizer of `e_last` in `GL_{m+1}(A)`.
* `frameEdgeStab A m`: the stabilizer of `e_last` and `e_{cs last}` in `GL_{m+2}(A)`.
* `frameTau A m`: the permutation unit of `swap(last, cs last)`, with `τ e_last = e_{cs last}`,
  `τ e_{cs last} = e_last` and `τ² = 1`.
* `frameEta A m : K →* K`, `k ↦ τ k τ⁻¹` (`frameTau_conj_mem`).

The block forms of `J` and `K` (Khanh's `k(a,b,H)`) are in `Frame.StabBlock`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

variable {A : Type*} [Ring A] {m : ℕ}

/-- `J`: the stabilizer of the base vertex `e_last` of `A^{m+1}`. -/
def frameVertexStab (A : Type*) [Ring A] (m : ℕ) :
    Subgroup (Matrix (Fin (m + 1)) (Fin (m + 1)) A)ˣ :=
  MulAction.stabilizer _ (Pi.single (Fin.last m) 1 : Fin (m + 1) → A)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameVertexStab

theorem mem_frameVertexStab_iff {g : (Matrix (Fin (m + 1)) (Fin (m + 1)) A)ˣ} :
    g ∈ frameVertexStab A m ↔
      g • (Pi.single (Fin.last m) 1 : Fin (m + 1) → A) = Pi.single (Fin.last m) 1 :=
  Iff.rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.mem_frameVertexStab_iff

/-- `K`: the stabilizer of the base edge `(e_last, e_{cs last})` of `A^{m+2}`. -/
def frameEdgeStab (A : Type*) [Ring A] (m : ℕ) :
    Subgroup (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) A)ˣ :=
  MulAction.stabilizer _ (Pi.single (Fin.last (m + 1)) 1 : Fin (m + 1 + 1) → A) ⊓
    MulAction.stabilizer _ (Pi.single (Fin.castSucc (Fin.last m)) 1 : Fin (m + 1 + 1) → A)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameEdgeStab

theorem mem_frameEdgeStab_iff {g : (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) A)ˣ} :
    g ∈ frameEdgeStab A m ↔
      g • (Pi.single (Fin.last (m + 1)) 1 : Fin (m + 1 + 1) → A) =
          Pi.single (Fin.last (m + 1)) 1 ∧
        g • (Pi.single (Fin.castSucc (Fin.last m)) 1 : Fin (m + 1 + 1) → A) =
          Pi.single (Fin.castSucc (Fin.last m)) 1 :=
  Iff.rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.mem_frameEdgeStab_iff

theorem frameEdgeStab_le_frameVertexStab : frameEdgeStab A m ≤ frameVertexStab A (m + 1) :=
  inf_le_left

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameEdgeStab_le_frameVertexStab

/-- `τ`: the permutation unit exchanging the base vertices `e_last` and `e_{cs last}`. -/
def frameTau (A : Type*) [Ring A] (m : ℕ) : (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) A)ˣ :=
  framePermUnit (Equiv.swap (Fin.last (m + 1)) (Fin.castSucc (Fin.last m)))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTau

theorem frameTau_smul_last :
    frameTau A m • (Pi.single (Fin.last (m + 1)) 1 : Fin (m + 1 + 1) → A) =
      Pi.single (Fin.castSucc (Fin.last m)) 1 := by
  rw [frameTau, framePermUnit_smul_single, Equiv.symm_swap, Equiv.swap_apply_left]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTau_smul_last

theorem frameTau_smul_castSucc :
    frameTau A m • (Pi.single (Fin.castSucc (Fin.last m)) 1 : Fin (m + 1 + 1) → A) =
      Pi.single (Fin.last (m + 1)) 1 := by
  rw [frameTau, framePermUnit_smul_single, Equiv.symm_swap, Equiv.swap_apply_right]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTau_smul_castSucc

theorem frameTau_mul_self : frameTau A m * frameTau A m = 1 :=
  framePermUnit_mul_self_of_mul_self (Equiv.swap_mul_self _ _)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTau_mul_self

theorem frameTau_inv : (frameTau A m)⁻¹ = frameTau A m :=
  inv_eq_of_mul_eq_one_right frameTau_mul_self

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTau_inv

/-- `τ` normalizes `K`. -/
theorem frameTau_conj_mem {k : (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) A)ˣ}
    (hk : k ∈ frameEdgeStab A m) :
    frameTau A m * k * (frameTau A m)⁻¹ ∈ frameEdgeStab A m := by
  rw [mem_frameEdgeStab_iff] at hk ⊢
  rw [frameTau_inv, mul_smul, mul_smul, mul_smul, mul_smul, frameTau_smul_last, hk.2,
    frameTau_smul_castSucc, hk.1, frameTau_smul_last]
  exact ⟨rfl, rfl⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTau_conj_mem

/-- `η : K →* K`, `k ↦ τ k τ⁻¹`. -/
def frameEta (A : Type*) [Ring A] (m : ℕ) : frameEdgeStab A m →* frameEdgeStab A m :=
  MonoidHom.mk' (fun k => ⟨frameTau A m * k * (frameTau A m)⁻¹, frameTau_conj_mem k.2⟩)
    (fun k l => Subtype.ext (show frameTau A m * ((k * l : frameEdgeStab A m) :
        (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) A)ˣ) * (frameTau A m)⁻¹ =
      (frameTau A m * k * (frameTau A m)⁻¹) * (frameTau A m * l * (frameTau A m)⁻¹) by
        simp only [Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left]))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameEta

theorem frameEta_apply (k : frameEdgeStab A m) :
    ((frameEta A m k : frameEdgeStab A m) : (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) A)ˣ) =
      frameTau A m * k * (frameTau A m)⁻¹ := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameEta_apply

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
