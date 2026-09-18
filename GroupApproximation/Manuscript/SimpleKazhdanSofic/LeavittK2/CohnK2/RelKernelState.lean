import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnK2.RelKernelSwap
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.Words
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Embedding
import GroupApproximation.Meta.AxiomGuard

/-!
# Moving matrix-unit roots to `p`-roots (lane `sk-cohn-02`, module 4)

Let `R` be a ring with Cohn data `D` (`e, f, e*, f*`, `p = 1 - ee* - ff*`).  Write `W α` for the
word `α`, `V α` for its coword and `u(α, β) = W α p V β`.  Fix `ω : Fin K → List (Fin 2)`.
The indices are `Fin (n + n K)`, with low indices `lo i = i` and high indices
`hi i t = n + (t + K i)`.

For `γ = (i, s)`, `relKer_w γ` is the swap `x_ab(A) x_ba(-B) x_ab(A)` with
`a = lo i`, `b = hi i s`, `A = W (ω s) p` and `B = p V (ω s)`.  Then `B A = p`, and `A B` is the
idempotent `u(ω s, ω s)`.

Conjugating `x_{lo i, lo j}(u(ω s, ω t))` by the swaps passes through four states
(`relKer_state … bi bj`):
* `ff`: `x_{lo i, lo j}(u(ω s, ω t))`;
* `tf`: `x_{hi i s, lo j}(-(p V(ω t)))`;
* `ft`: `x_{lo i, hi j t}(-(W(ω s) p))`;
* `tt`: `x_{hi i s, hi j t}(p)`.

Each swap either flips one flag (`relKer_stepI`, `relKer_stepJ`) or fixes the state
(`relKer_stepFix`, which needs `ω` injective).  All ring identities reduce to the sandwich
`p V α W β p = δ_{αβ} p`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

/-! ### Index maps -/

/-- The low copy `Fin n → Fin (n + n K)`. -/
def relKer_lo (n K : ℕ) (i : Fin n) : Fin (n + n * K) :=
  Fin.castLEEmb (Nat.le_add_right n (n * K)) i

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_lo

/-- The high copies `Fin n × Fin K → Fin (n + n K)`. -/
def relKer_hi (n K : ℕ) (i : Fin n) (t : Fin K) : Fin (n + n * K) :=
  Fin.natAdd n (finProdFinEquiv (i, t))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_hi

theorem relKer_lo_inj {n K : ℕ} {i j : Fin n} (h : relKer_lo n K i = relKer_lo n K j) :
    i = j :=
  (Fin.castLEEmb (Nat.le_add_right n (n * K))).injective h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_lo_inj

theorem relKer_hi_inj {n K : ℕ} {i j : Fin n} {s t : Fin K}
    (h : relKer_hi n K i s = relKer_hi n K j t) : i = j ∧ s = t := by
  have hv : (relKer_hi n K i s).val = (relKer_hi n K j t).val := congrArg Fin.val h
  have h' : finProdFinEquiv (i, s) = finProdFinEquiv (j, t) := by
    apply Fin.ext
    change n + (finProdFinEquiv (i, s)).val = n + (finProdFinEquiv (j, t)).val at hv
    omega
  exact Prod.mk.inj (finProdFinEquiv.injective h')

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_hi_inj

theorem relKer_lo_ne_hi {n K : ℕ} (i j : Fin n) (t : Fin K) :
    relKer_lo n K i ≠ relKer_hi n K j t := by
  intro h
  have hv : (relKer_lo n K i).val = (relKer_hi n K j t).val := congrArg Fin.val h
  change i.val = n + (finProdFinEquiv (j, t)).val at hv
  have hi := i.isLt
  omega

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_lo_ne_hi

theorem relKer_lo_ne {n K : ℕ} {i j : Fin n} (h : i ≠ j) : relKer_lo n K i ≠ relKer_lo n K j :=
  fun e => h (relKer_lo_inj e)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_lo_ne

theorem relKer_hi_ne {n K : ℕ} {i j : Fin n} (h : i ≠ j) (s t : Fin K) :
    relKer_hi n K i s ≠ relKer_hi n K j t :=
  fun e => h (relKer_hi_inj e).1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_hi_ne

/-! ### Ring identities -/

section Ring

variable {R : Type*} [Ring R] (D : CohnRelativeK1.CohnTwoData R)

/-- `p (p X) = p X`. -/
theorem relKer_pp (X : R) : D.p * (D.p * X) = D.p * X := by
  rw [← mul_assoc, D.p_mul_p]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_pp

/-- `p V α W α p = p`. -/
theorem relKer_ss0 (α : List (Fin 2)) : D.p * (D.coword α * (D.word α * D.p)) = D.p := by
  rw [D.sandwich α α, if_pos rfl]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_ss0

/-- `p V α W α p X = p X`. -/
theorem relKer_ss (α : List (Fin 2)) (X : R) :
    D.p * (D.coword α * (D.word α * (D.p * X))) = D.p * X := by
  calc D.p * (D.coword α * (D.word α * (D.p * X)))
      = D.p * (D.coword α * (D.word α * D.p)) * X := by simp only [mul_assoc]
    _ = D.p * X := by rw [relKer_ss0]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_ss

/-- `p V α W β p = 0` for `α ≠ β`. -/
theorem relKer_sn0 {α β : List (Fin 2)} (h : α ≠ β) :
    D.p * (D.coword α * (D.word β * D.p)) = 0 := by
  rw [D.sandwich α β, if_neg h]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_sn0

/-- `p V α W β p X = 0` for `α ≠ β`. -/
theorem relKer_sn {α β : List (Fin 2)} (h : α ≠ β) (X : R) :
    D.p * (D.coword α * (D.word β * (D.p * X))) = 0 := by
  calc D.p * (D.coword α * (D.word β * (D.p * X)))
      = D.p * (D.coword α * (D.word β * D.p)) * X := by simp only [mul_assoc]
    _ = 0 := by rw [relKer_sn0 D h, zero_mul]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_sn

end Ring

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
