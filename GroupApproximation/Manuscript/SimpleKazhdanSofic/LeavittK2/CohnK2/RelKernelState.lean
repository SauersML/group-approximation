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

set_option linter.unusedSimpArgs false

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

/-- `u(α, β) W γ p = 0` for `β ≠ γ`. -/
theorem relKer_Z1 {α β γ : List (Fin 2)} (h : β ≠ γ) :
    D.unit α β * (D.word γ * D.p) = 0 := by
  calc D.unit α β * (D.word γ * D.p)
      = D.word α * (D.p * (D.coword β * (D.word γ * D.p))) := by
        simp only [CohnRelativeK1.CohnTwoData.unit, mul_assoc]
    _ = 0 := by rw [relKer_sn0 D h, mul_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_Z1

/-- `-(p V β) W γ p = 0` for `β ≠ γ`. -/
theorem relKer_Z2 {β γ : List (Fin 2)} (h : β ≠ γ) :
    -(D.p * D.coword β) * (D.word γ * D.p) = 0 := by
  rw [neg_mul, mul_assoc, relKer_sn0 D h, neg_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_Z2

/-- `p V γ u(α, β) = 0` for `γ ≠ α`. -/
theorem relKer_Z3 {γ α β : List (Fin 2)} (h : γ ≠ α) :
    D.p * D.coword γ * D.unit α β = 0 := by
  calc D.p * D.coword γ * D.unit α β
      = D.p * (D.coword γ * (D.word α * D.p)) * D.coword β := by
        simp only [CohnRelativeK1.CohnTwoData.unit, mul_assoc]
    _ = 0 := by rw [relKer_sn0 D h, zero_mul]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_Z3

/-- `p V γ (-(W α p)) = 0` for `γ ≠ α`. -/
theorem relKer_Z4 {γ α : List (Fin 2)} (h : γ ≠ α) :
    D.p * D.coword γ * -(D.word α * D.p) = 0 := by
  rw [mul_neg, mul_assoc, relKer_sn0 D h, neg_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_Z4

end Ring

/-! ### Explicit swap conjugations -/

section Conj

variable {J R : Type*} [Fintype J] [DecidableEq J] [Ring R] (D : CohnRelativeK1.CohnTwoData R)

/-- Column move: `x_ac(u(α, β)) ↦ x_bc(-(p V β))`. -/
theorem relKer_colFF (a b c : J) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (α β : List (Fin 2)) :
    relKer_swap a b hab (D.word α * D.p) (D.p * D.coword α) * x a c hac (D.unit α β) *
        (relKer_swap a b hab (D.word α * D.p) (D.p * D.coword α))⁻¹ =
      x b c hbc (-(D.p * D.coword β)) := by
  have hBc : D.p * D.coword α * D.unit α β = D.p * D.coword β := by
    simp only [CohnRelativeK1.CohnTwoData.unit, mul_assoc, relKer_ss D]
  have hc : D.word α * D.p * (D.p * D.coword α * D.unit α β) = D.unit α β := by
    rw [hBc]
    simp only [CohnRelativeK1.CohnTwoData.unit, mul_assoc, relKer_pp D]
  rw [relKer_swap_conj_col a b c hab hac hbc (D.word α * D.p) (D.p * D.coword α)
    (D.unit α β) hc, hBc]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_colFF

/-- Column move: `x_ac(-(W α p)) ↦ x_bc(p)`. -/
theorem relKer_colFT (a b c : J) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (α : List (Fin 2)) :
    relKer_swap a b hab (D.word α * D.p) (D.p * D.coword α) * x a c hac (-(D.word α * D.p)) *
        (relKer_swap a b hab (D.word α * D.p) (D.p * D.coword α))⁻¹ = x b c hbc D.p := by
  have hBc : D.p * D.coword α * -(D.word α * D.p) = -D.p := by
    rw [mul_neg, mul_assoc, relKer_ss0 D]
  have hc : D.word α * D.p * (D.p * D.coword α * -(D.word α * D.p)) = -(D.word α * D.p) := by
    rw [hBc, mul_neg, mul_assoc, D.p_mul_p]
  rw [relKer_swap_conj_col a b c hab hac hbc (D.word α * D.p) (D.p * D.coword α)
    (-(D.word α * D.p)) hc, hBc, neg_neg]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_colFT

/-- Row move: `x_ra(u(α, β)) ↦ x_rb(-(W α p))`. -/
theorem relKer_rowFF (r a b : J) (hab : a ≠ b) (hra : r ≠ a) (hrb : r ≠ b)
    (α β : List (Fin 2)) :
    relKer_swap a b hab (D.word β * D.p) (D.p * D.coword β) * x r a hra (D.unit α β) *
        (relKer_swap a b hab (D.word β * D.p) (D.p * D.coword β))⁻¹ =
      x r b hrb (-(D.word α * D.p)) := by
  have hcA : D.unit α β * (D.word β * D.p) = D.word α * D.p := by
    simp only [CohnRelativeK1.CohnTwoData.unit, mul_assoc, relKer_ss0 D]
  have hc : D.unit α β * (D.word β * D.p) * (D.p * D.coword β) = D.unit α β := by
    rw [hcA]
    simp only [CohnRelativeK1.CohnTwoData.unit, mul_assoc, relKer_pp D]
  rw [relKer_swap_conj_row r a b hab hra hrb (D.word β * D.p) (D.p * D.coword β)
    (D.unit α β) hc, hcA]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_rowFF

/-- Row move: `x_ra(-(p V β)) ↦ x_rb(p)`. -/
theorem relKer_rowTF (r a b : J) (hab : a ≠ b) (hra : r ≠ a) (hrb : r ≠ b)
    (β : List (Fin 2)) :
    relKer_swap a b hab (D.word β * D.p) (D.p * D.coword β) * x r a hra (-(D.p * D.coword β)) *
        (relKer_swap a b hab (D.word β * D.p) (D.p * D.coword β))⁻¹ = x r b hrb D.p := by
  have hcA : -(D.p * D.coword β) * (D.word β * D.p) = -D.p := by
    rw [neg_mul, mul_assoc, relKer_ss0 D]
  have hc : -(D.p * D.coword β) * (D.word β * D.p) * (D.p * D.coword β) =
      -(D.p * D.coword β) := by
    rw [hcA, neg_mul, ← mul_assoc, D.p_mul_p]
  rw [relKer_swap_conj_row r a b hab hra hrb (D.word β * D.p) (D.p * D.coword β)
    (-(D.p * D.coword β)) hc, hcA, neg_neg]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_rowTF

/-- The fixing criterion in the form used below. -/
theorem relKer_swap_fix' (a b : J) (hab : a ≠ b) (A B : R) (r c : J) (hrc : r ≠ c) (e : R)
    (hbr : b ≠ r) (hcb : c ≠ b) (h2 : c = a → e * A = 0) (h3 : a = r → B * e = 0) :
    relKer_swap a b hab A B * x r c hrc e * (relKer_swap a b hab A B)⁻¹ = x r c hrc e :=
  relKer_swap_fix a b hab A B r c hrc e (fun h => absurd h hbr) h2 h3 (fun h => absurd h hcb)
    (fun h => hbr h.1) (fun h => hcb h.2)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_swap_fix'

end Conj

/-! ### The swaps and the four states -/

section State

variable {R : Type*} [Ring R] (D : CohnRelativeK1.CohnTwoData R) {n K : ℕ}
  (ω : Fin K → List (Fin 2))

/-- The swap attached to `γ = (i, s)`: it exchanges `lo i` and `hi i s`. -/
def relKer_w (γ : Fin n × Fin K) : SteinbergGroup (Fin (n + n * K)) R :=
  relKer_swap (relKer_lo n K γ.1) (relKer_hi n K γ.1 γ.2) (relKer_lo_ne_hi γ.1 γ.1 γ.2)
    (D.word (ω γ.2) * D.p) (D.p * D.coword (ω γ.2))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_w

/-- The four states of `x_{lo i, lo j}(u(ω s, ω t))`. -/
def relKer_state (i j : Fin n) (hij : i ≠ j) (s t : Fin K) :
    Bool → Bool → SteinbergGroup (Fin (n + n * K)) R
  | false, false => x (relKer_lo n K i) (relKer_lo n K j) (relKer_lo_ne hij) (D.unit (ω s) (ω t))
  | true, false => x (relKer_hi n K i s) (relKer_lo n K j) (relKer_lo_ne_hi j i s).symm
      (-(D.p * D.coword (ω t)))
  | false, true => x (relKer_lo n K i) (relKer_hi n K j t) (relKer_lo_ne_hi i j t)
      (-(D.word (ω s) * D.p))
  | true, true => x (relKer_hi n K i s) (relKer_hi n K j t) (relKer_hi_ne hij s t) D.p

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_state

/-- The swap at `(i, s)` sets the first flag. -/
theorem relKer_stepI (i j : Fin n) (hij : i ≠ j) (s t : Fin K) (b : Bool) :
    relKer_w D ω (i, s) * relKer_state D ω i j hij s t false b * (relKer_w D ω (i, s))⁻¹ =
      relKer_state D ω i j hij s t true b := by
  cases b with
  | false =>
      exact relKer_colFF D (relKer_lo n K i) (relKer_hi n K i s) (relKer_lo n K j)
        (relKer_lo_ne_hi i i s) (relKer_lo_ne hij) (relKer_lo_ne_hi j i s).symm (ω s) (ω t)
  | true =>
      exact relKer_colFT D (relKer_lo n K i) (relKer_hi n K i s) (relKer_hi n K j t)
        (relKer_lo_ne_hi i i s) (relKer_lo_ne_hi i j t) (relKer_hi_ne hij s t) (ω s)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_stepI

/-- The swap at `(j, t)` sets the second flag. -/
theorem relKer_stepJ (i j : Fin n) (hij : i ≠ j) (s t : Fin K) (b : Bool) :
    relKer_w D ω (j, t) * relKer_state D ω i j hij s t b false * (relKer_w D ω (j, t))⁻¹ =
      relKer_state D ω i j hij s t b true := by
  cases b with
  | false =>
      exact relKer_rowFF D (relKer_lo n K i) (relKer_lo n K j) (relKer_hi n K j t)
        (relKer_lo_ne_hi j j t) (relKer_lo_ne hij) (relKer_lo_ne_hi i j t) (ω s) (ω t)
  | true =>
      exact relKer_rowTF D (relKer_hi n K i s) (relKer_lo n K j) (relKer_hi n K j t)
        (relKer_lo_ne_hi j j t) (relKer_lo_ne_hi j i s).symm (relKer_hi_ne hij s t) (ω t)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_stepJ

/-- Any other swap fixes every state (this needs `ω` injective). -/
theorem relKer_stepFix (hω : Function.Injective ω) (i j : Fin n) (hij : i ≠ j) (s t : Fin K)
    (i' : Fin n) (s' : Fin K) (hI : (i', s') ≠ (i, s)) (hJ : (i', s') ≠ (j, t)) (bi bj : Bool) :
    relKer_w D ω (i', s') * relKer_state D ω i j hij s t bi bj * (relKer_w D ω (i', s'))⁻¹ =
      relKer_state D ω i j hij s t bi bj := by
  have his : relKer_hi n K i' s' ≠ relKer_hi n K i s := fun h =>
    hI (by obtain ⟨e1, e2⟩ := relKer_hi_inj h; rw [e1, e2])
  have hjt : relKer_hi n K i' s' ≠ relKer_hi n K j t := fun h =>
    hJ (by obtain ⟨e1, e2⟩ := relKer_hi_inj h; rw [e1, e2])
  have hsI : relKer_lo n K i' = relKer_lo n K i → ω s' ≠ ω s := fun h e =>
    hI (by rw [relKer_lo_inj h, hω e])
  have hsJ : relKer_lo n K j = relKer_lo n K i' → ω t ≠ ω s' := fun h e =>
    hJ (by rw [← relKer_lo_inj h, hω e])
  have hbr0 : relKer_hi n K i' s' ≠ relKer_lo n K i := (relKer_lo_ne_hi i i' s').symm
  have hcb0 : relKer_lo n K j ≠ relKer_hi n K i' s' := relKer_lo_ne_hi j i' s'
  match bi, bj with
  | false, false =>
      exact relKer_swap_fix' (relKer_lo n K i') (relKer_hi n K i' s') (relKer_lo_ne_hi i' i' s')
        (D.word (ω s') * D.p) (D.p * D.coword (ω s')) (relKer_lo n K i) (relKer_lo n K j)
        (relKer_lo_ne hij) (D.unit (ω s) (ω t)) hbr0 hcb0
        (fun h => relKer_Z1 D (hsJ h)) (fun h => relKer_Z3 D (hsI h))
  | false, true =>
      exact relKer_swap_fix' (relKer_lo n K i') (relKer_hi n K i' s') (relKer_lo_ne_hi i' i' s')
        (D.word (ω s') * D.p) (D.p * D.coword (ω s')) (relKer_lo n K i) (relKer_hi n K j t)
        (relKer_lo_ne_hi i j t) (-(D.word (ω s) * D.p)) hbr0 (fun h => hjt h.symm)
        (fun h => absurd h.symm (relKer_lo_ne_hi i' j t)) (fun h => relKer_Z4 D (hsI h))
  | true, false =>
      exact relKer_swap_fix' (relKer_lo n K i') (relKer_hi n K i' s') (relKer_lo_ne_hi i' i' s')
        (D.word (ω s') * D.p) (D.p * D.coword (ω s')) (relKer_hi n K i s) (relKer_lo n K j)
        (relKer_lo_ne_hi j i s).symm (-(D.p * D.coword (ω t))) his hcb0
        (fun h => relKer_Z2 D (hsJ h)) (fun h => absurd h (relKer_lo_ne_hi i' i s))
  | true, true =>
      exact relKer_swap_fix' (relKer_lo n K i') (relKer_hi n K i' s') (relKer_lo_ne_hi i' i' s')
        (D.word (ω s') * D.p) (D.p * D.coword (ω s')) (relKer_hi n K i s) (relKer_hi n K j t)
        (relKer_hi_ne hij s t) D.p his (fun h => hjt h.symm)
        (fun h => absurd h.symm (relKer_lo_ne_hi i' j t))
        (fun h => absurd h (relKer_lo_ne_hi i' i s))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_stepFix

end State

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
