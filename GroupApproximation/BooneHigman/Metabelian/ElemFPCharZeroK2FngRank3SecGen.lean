import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngGtOneRank3Core
import Mathlib.Tactic.FinCases
import GroupApproximation.Meta.AxiomGuard

/-!
# Four generators suffice for the checks (lane `bh-met-93x`, part 2)

Indices are `0, 1, 2 : Fin 3`.  Let `H` be a subgroup of `St_3(S)` containing
`x₀₁(1)`, `x₁₂(1)`, `x₂₀(1)` and `x₀₁(a)`.  Then `H` contains every `x_ij(1)` and every
`x_ij(a)` (`czK2FngRank3Sec_all_of_cyclic`).  The proof uses only the commutator relation
`[x_il(b), x_lj(c)] = x_ij(bc)` (`czK2FngRank3Sec_comm_mem`), eight times:

* `x₀₂(1) = [x₀₁(1), x₁₂(1)]`, `x₁₀(1) = [x₁₂(1), x₂₀(1)]`, `x₂₁(1) = [x₂₀(1), x₀₁(1)]`;
* `x₀₂(a) = [x₀₁(a), x₁₂(1)]`, `x₂₁(a) = [x₂₀(1), x₀₁(a)]`, `x₁₂(a) = [x₁₀(1), x₀₂(a)]`,
  `x₂₀(a) = [x₂₁(a), x₁₀(1)]`, `x₁₀(a) = [x₁₂(a), x₂₀(1)]`.

The script `$SP/bh-met-93x/truth_check.py` checks these identities on matrices.  It also checks
in `SL_3(F_q)`, `q = 2, 3, 5`, that the four elements generate the same subgroup as the twelve.

Proved outright.  There are no hypotheses and no literature inputs.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

/-- A subgroup containing `x_il(a)` and `x_lj(b)` contains `x_ij(ab)`. -/
theorem czK2FngRank3Sec_comm_mem {S : Type*} [CommRing S]
    (H : Subgroup (SteinbergGroup (Fin 3) S)) (i l j : Fin 3) (hil : i ≠ l) (hlj : l ≠ j)
    (hij : i ≠ j) {a b : S} (ha : x i l hil a ∈ H) (hb : x l j hlj b ∈ H) :
    x i j hij (a * b) ∈ H := by
  rw [← x_commutator i l j hil hlj hij, commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Sec_comm_mem

/-- **Four generators.**  A subgroup of `St_3(S)` containing `x₀₁(1)`, `x₁₂(1)`, `x₂₀(1)` and
`x₀₁(a)` contains every `x_ij(1)` and every `x_ij(a)`. -/
theorem czK2FngRank3Sec_all_of_cyclic {S : Type*} [CommRing S]
    (H : Subgroup (SteinbergGroup (Fin 3) S)) (a : S)
    (h01 : x (0 : Fin 3) 1 (by decide) (1 : S) ∈ H)
    (h12 : x (1 : Fin 3) 2 (by decide) (1 : S) ∈ H)
    (h20 : x (2 : Fin 3) 0 (by decide) (1 : S) ∈ H)
    (ha01 : x (0 : Fin 3) 1 (by decide) a ∈ H) :
    ∀ (i j : Fin 3) (h : i ≠ j), x i j h 1 ∈ H ∧ x i j h a ∈ H := by
  have h02 : x (0 : Fin 3) 2 (by decide) (1 : S) ∈ H := by
    have e := czK2FngRank3Sec_comm_mem H 0 1 2 (by decide) (by decide) (by decide) h01 h12
    rwa [mul_one] at e
  have h10 : x (1 : Fin 3) 0 (by decide) (1 : S) ∈ H := by
    have e := czK2FngRank3Sec_comm_mem H 1 2 0 (by decide) (by decide) (by decide) h12 h20
    rwa [mul_one] at e
  have h21 : x (2 : Fin 3) 1 (by decide) (1 : S) ∈ H := by
    have e := czK2FngRank3Sec_comm_mem H 2 0 1 (by decide) (by decide) (by decide) h20 h01
    rwa [mul_one] at e
  have ha02 : x (0 : Fin 3) 2 (by decide) a ∈ H := by
    have e := czK2FngRank3Sec_comm_mem H 0 1 2 (by decide) (by decide) (by decide) ha01 h12
    rwa [mul_one] at e
  have ha21 : x (2 : Fin 3) 1 (by decide) a ∈ H := by
    have e := czK2FngRank3Sec_comm_mem H 2 0 1 (by decide) (by decide) (by decide) h20 ha01
    rwa [one_mul] at e
  have ha12 : x (1 : Fin 3) 2 (by decide) a ∈ H := by
    have e := czK2FngRank3Sec_comm_mem H 1 0 2 (by decide) (by decide) (by decide) h10 ha02
    rwa [one_mul] at e
  have ha20 : x (2 : Fin 3) 0 (by decide) a ∈ H := by
    have e := czK2FngRank3Sec_comm_mem H 2 1 0 (by decide) (by decide) (by decide) ha21 h10
    rwa [mul_one] at e
  have ha10 : x (1 : Fin 3) 0 (by decide) a ∈ H := by
    have e := czK2FngRank3Sec_comm_mem H 1 2 0 (by decide) (by decide) (by decide) ha12 h20
    rwa [mul_one] at e
  intro i j
  fin_cases i <;> fin_cases j <;> intro h
  all_goals first
    | exact (h rfl).elim
    | exact ⟨h01, ha01⟩
    | exact ⟨h02, ha02⟩
    | exact ⟨h10, ha10⟩
    | exact ⟨h12, ha12⟩
    | exact ⟨h20, ha20⟩
    | exact ⟨h21, ha21⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Sec_all_of_cyclic

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
