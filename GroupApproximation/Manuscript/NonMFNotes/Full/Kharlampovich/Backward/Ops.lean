import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.End
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ReduceModChar

/-!
# Local operators on functions of the KMS model

Input for the "if" direction of KMS Theorem `tmm`(b) (`l654`, `l789` of
Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506, Sec. 4.1), used in
`thm:fixed-radical-membership` of `non_mf_group_notes.tex`.

The letters of `L_1 ∪ L_2` act on `𝔽_2`-valued functions `φ` on pairs `(v, c)`.
Here `v : Fin K → Tri` carries one auxiliary coordinate with three values per glass,
and `c` is a class of words.  A small letter at coordinate `n` changes `φ` only at
active classes `c` (`act c`).  There the new value at `(v, c)` is a fixed linear
combination (a table `Tab`) of the values `φ (v[n ↦ s]) c`, `s = 1, 2, 3`, and of
`φ v (σ c)`, where `σ` appends the letter to the class.

This file proves the generic facts:
* two tables that are inverse give inverse operators (`opL_opL`);
* operators at different coordinates commute (`opL_comm_ne`);
* operators at the same coordinate commute when their tables do (`opL_comm_self`);
* the operator `φ ↦ φ + φ ∘ β` of a letter `A_i` is an involution (`opB_opB`).
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

namespace Backward

/-- Closes ring identities over `ZMod 2`, including those using `2 = 0`. -/
macro "khbw_ring" : tactic =>
  `(tactic| first | ring1 | grind | (ring_nf; reduce_mod_char; done))

/-- The three values of an auxiliary coordinate (KMS `l789`). -/
inductive Tri : Type
  | z1
  | z2
  | z3
  deriving DecidableEq

/-- Case split on a value of `Tri`. -/
def Tri.sel {α : Sort*} : Tri → α → α → α → α
  | .z1, x, _, _ => x
  | .z2, _, y, _ => y
  | .z3, _, _, z => z

theorem Tri.sel_z1 {α : Sort*} (x y z : α) : Tri.sel .z1 x y z = x := rfl

theorem Tri.sel_z2 {α : Sort*} (x y z : α) : Tri.sel .z2 x y z = y := rfl

theorem Tri.sel_z3 {α : Sort*} (x y z : α) : Tri.sel .z3 x y z = z := rfl

variable {K : ℕ}

/-- `𝔽_2`-valued functions on the index set `(Fin K → Tri) × C`. -/
abbrev Fn (K : ℕ) (C : Type*) : Type _ := (Fin K → Tri) → C → ZMod 2

/-- A local rule: the coefficients `L t s` of the three values `φ (v[n ↦ s]) c`
and the coefficient `e t` of the shifted value, when `v n = t`. -/
structure Tab : Type where
  /-- Coefficient of the value at `v[n ↦ s]`, when `v n = t`. -/
  L : Tri → Tri → ZMod 2
  /-- Coefficient of the value at the shifted class, when `v n = t`. -/
  e : Tri → ZMod 2

/-- Evaluate a table. -/
def Tab.app (T : Tab) (t : Tri) (g : Tri → ZMod 2) (y : ZMod 2) : ZMod 2 :=
  T.L t .z1 * g .z1 + T.L t .z2 * g .z2 + T.L t .z3 * g .z3 + T.e t * y

section Local

variable {C : Type*} (n : Fin K) (act : C → Prop) [DecidablePred act] (σ : C → C)

/-- The local operator of a small letter at coordinate `n` (KMS `l789`). -/
def opL (T : Tab) (φ : Fn K C) : Fn K C := fun v c ↦
  if act c then T.app (v n) (fun s ↦ φ (Function.update v n s) c) (φ v (σ c)) else φ v c

theorem opL_of_not (T : Tab) (φ : Fn K C) (v : Fin K → Tri) {c : C} (hc : ¬ act c) :
    opL n act σ T φ v c = φ v c := by
  simp only [opL, hc, ↓reduceIte]

/-- Inverse tables give inverse operators. -/
theorem opL_opL {T1 T2 : Tab} (hσ : ∀ c, act (σ c) ↔ act c)
    (hT : ∀ t g h y, T2.app t (fun s ↦ T1.app s g (h s)) (T1.app t h y) = g t)
    (φ : Fn K C) : opL n act σ T2 (opL n act σ T1 φ) = φ := by
  funext v c
  by_cases hc : act c
  · have hc' : act (σ c) := (hσ c).2 hc
    simp only [opL, hc, hc', ↓reduceIte, Function.update_self, Function.update_idem]
    have key := hT (v n) (fun s ↦ φ (Function.update v n s) c)
      (fun s ↦ φ (Function.update v n s) (σ c)) (φ v (σ (σ c)))
    rw [Function.update_eq_self] at key
    exact key
  · simp only [opL, hc, ↓reduceIte]

/-- Operators at different coordinates commute. -/
theorem opL_comm_ne {m : Fin K} (hnm : n ≠ m) {act' : C → Prop} [DecidablePred act']
    {σ' : C → C} (h1 : ∀ c, act' (σ c) ↔ act' c) (h2 : ∀ c, act (σ' c) ↔ act c)
    (hσ : ∀ c, act c → act' c → σ' (σ c) = σ (σ' c)) (T T' : Tab) (φ : Fn K C) :
    opL n act σ T (opL m act' σ' T' φ) = opL m act' σ' T' (opL n act σ T φ) := by
  funext v c
  by_cases hc : act c
  · by_cases hc' : act' c
    · have e1 : act' (σ c) := (h1 c).2 hc'
      have e2 : act (σ' c) := (h2 c).2 hc
      simp only [opL, hc, hc', e1, e2, ↓reduceIte, Function.update_of_ne hnm,
        Function.update_of_ne hnm.symm, Function.update_comm hnm, hσ c hc hc', Tab.app]
      ring
    · have e1 : ¬ act' (σ c) := fun h ↦ hc' ((h1 c).1 h)
      simp only [opL, hc, hc', e1, ↓reduceIte]
  · by_cases hc' : act' c
    · have e2 : ¬ act (σ' c) := fun h ↦ hc ((h2 c).1 h)
      simp only [opL, hc, hc', e2, ↓reduceIte]
    · simp only [opL, hc, hc', ↓reduceIte]

/-- Operators at the same coordinate commute when their tables commute. -/
theorem opL_comm_self (h0 : ∀ c, act (σ c) ↔ act c) {act' : C → Prop} [DecidablePred act']
    {σ' : C → C} (h1 : ∀ c, act' (σ c) ↔ act' c) (h2 : ∀ c, act (σ' c) ↔ act c)
    (hσ : ∀ c, act c → act' c → σ' c = σ c) {T T' : Tab}
    (hT : ∀ t g h y, T.app t (fun s ↦ T'.app s g (h s)) (T'.app t h y) =
      T'.app t (fun s ↦ T.app s g (h s)) (T.app t h y)) (φ : Fn K C) :
    opL n act σ T (opL n act' σ' T' φ) = opL n act' σ' T' (opL n act σ T φ) := by
  funext v c
  by_cases hc : act c
  · by_cases hc' : act' c
    · have e0 : act (σ c) := (h0 c).2 hc
      have e1 : act' (σ c) := (h1 c).2 hc'
      have e2 : act (σ' c) := (h2 c).2 hc
      have f1 : σ' c = σ c := hσ c hc hc'
      have f2 : σ' (σ c) = σ (σ c) := hσ (σ c) e0 e1
      simp only [opL, hc, hc', e1, e2, ↓reduceIte, Function.update_self, Function.update_idem]
      rw [f2, f1]
      exact hT (v n) (fun s ↦ φ (Function.update v n s) c)
        (fun s ↦ φ (Function.update v n s) (σ c)) (φ v (σ (σ c)))
    · have e1 : ¬ act' (σ c) := fun h ↦ hc' ((h1 c).1 h)
      simp only [opL, hc, hc', e1, ↓reduceIte]
  · by_cases hc' : act' c
    · have e2 : ¬ act (σ' c) := fun h ↦ hc ((h2 c).1 h)
      simp only [opL, hc, hc', e2, ↓reduceIte]
    · simp only [opL, hc, hc', ↓reduceIte]

/-- The permutation of a small letter, from a table and its inverse table. -/
def permL (T T' : Tab) (hσ : ∀ c, act (σ c) ↔ act c)
    (hT : ∀ t g h y, T'.app t (fun s ↦ T.app s g (h s)) (T.app t h y) = g t)
    (hT' : ∀ t g h y, T.app t (fun s ↦ T'.app s g (h s)) (T'.app t h y) = g t) :
    Equiv.Perm (Fn K C) where
  toFun := opL n act σ T
  invFun := opL n act σ T'
  left_inv := opL_opL n act σ hσ hT
  right_inv := opL_opL n act σ hσ hT'

theorem permL_apply (T T' : Tab) (hσ : ∀ c, act (σ c) ↔ act c)
    (hT : ∀ t g h y, T'.app t (fun s ↦ T.app s g (h s)) (T.app t h y) = g t)
    (hT' : ∀ t g h y, T.app t (fun s ↦ T'.app s g (h s)) (T'.app t h y) = g t)
    (φ : Fn K C) : permL n act σ T T' hσ hT hT' φ = opL n act σ T φ := rfl

theorem permL_symm_apply (T T' : Tab) (hσ : ∀ c, act (σ c) ↔ act c)
    (hT : ∀ t g h y, T'.app t (fun s ↦ T.app s g (h s)) (T.app t h y) = g t)
    (hT' : ∀ t g h y, T.app t (fun s ↦ T'.app s g (h s)) (T'.app t h y) = g t)
    (φ : Fn K C) : (permL n act σ T T' hσ hT hT').symm φ = opL n act σ T' φ := rfl

end Local

section Big

variable {C : Type*} (act : C → Prop) [DecidablePred act] (β : C → C)

/-- The operator `φ ↦ φ + φ ∘ β` of a letter `A_i` on active classes (KMS `l789`). -/
def opB (φ : Fn K C) : Fn K C := fun v c ↦
  if act c then φ v c + φ v (β c) else φ v c

theorem opB_opB (hβ : ∀ c, act c → ¬ act (β c)) (φ : Fn K C) :
    opB act β (opB act β φ) = φ := by
  funext v c
  by_cases hc : act c
  · have hc' : ¬ act (β c) := hβ c hc
    simp only [opB, hc, hc', ↓reduceIte]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · simp only [opB, hc, ↓reduceIte]

/-- The involution of a letter `A_i`. -/
def permB (hβ : ∀ c, act c → ¬ act (β c)) : Equiv.Perm (Fn K C) where
  toFun := opB act β
  invFun := opB act β
  left_inv := opB_opB act β hβ
  right_inv := opB_opB act β hβ

theorem permB_apply (hβ : ∀ c, act c → ¬ act (β c)) (φ : Fn K C) :
    permB act β hβ φ = opB act β φ := rfl

theorem permB_symm_apply (hβ : ∀ c, act c → ¬ act (β c)) (φ : Fn K C) :
    (permB act β hβ).symm φ = opB act β φ := rfl

end Big

end Backward

end KMS

end GroupApproximation.Full.Kharlampovich
