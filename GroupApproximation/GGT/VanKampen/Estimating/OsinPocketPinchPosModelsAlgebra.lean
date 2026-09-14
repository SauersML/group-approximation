import GroupApproximation.GGT.VanKampen.SymmetricLabelAlphabet
import GroupApproximation.Algebra.WordMetric
import Mathlib.GroupTheory.FreeGroup.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# The group of the ε = 1 counterexample to the positive pinch

The counterexample to `PocketPinchLabelledPosStatement` at `ε = 1` lives over the free group on six
letters `a, b, d, e, x, y`, with the relator words `P = a a b` and `Q = d d e` and the boundary
letter `c = x P x⁻¹ y Q y⁻¹`.  A simple pocket face set in an O-equivalent copy would give, for the
kept cell and the source cell, a relation `α · p⁻¹ · β ~ r^{±1}`, where `α` and `β` have word norm at
most one, `p` is a proper cyclic arc of the source word and `r` is the kept word.  This module shows
that no such relation holds, with homomorphisms only:

* exponent sums over `d, e` (resp. `a, b`) exclude the case with no `c` among `α, β`;
* the kill map `killP : G →* Perm (Fin 4)`, sending `a, b` to a 4-cycle, `x` to a transposition and
  `d, e, y` to `1`, excludes the cases with a `c`, since `x P x⁻¹` leaves the image of `F(a, b)`
  (resp. `killQ` for the kept word `P`).

## Manuscript status

Model test for infrastructure of `thm:hull` (Hull's small cancellation theorem, through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketPinchPosModels

open GGT

/-- The free group on the six letters `a, b, d, e, x, y`. -/
abbrev G := FreeGroup (Fin 6)

def ga : G := FreeGroup.of 0
def gb : G := FreeGroup.of 1
def gd : G := FreeGroup.of 2
def ge : G := FreeGroup.of 3
def gx : G := FreeGroup.of 4
def gy : G := FreeGroup.of 5

/-- The relator word `P = a a b` of the source cell. -/
def pWord : List (RelLetter G Empty) := [.base ga, .base ga, .base gb]
/-- The relator word `Q = d d e` of the kept cell. -/
def qWord : List (RelLetter G Empty) := [.base gd, .base gd, .base ge]

def gP : G := ga * ga * gb
def gQ : G := gd * gd * ge

/-- The boundary letter `c = x P x⁻¹ y Q y⁻¹`. -/
def gc : G := gx * gP * gx⁻¹ * gy * gQ * gy⁻¹

theorem listVal_pWord : RelLetter.listVal pWord = gP := by
  simp [RelLetter.listVal, pWord, RelLetter.val, gP, mul_assoc]

theorem listVal_qWord : RelLetter.listVal qWord = gQ := by
  simp [RelLetter.listVal, qWord, RelLetter.val, gQ, mul_assoc]

/-- The base letters: the generators, `c`, and their inverses. -/
def baseSet : Set G :=
  {ga, ga⁻¹, gb, gb⁻¹, gd, gd⁻¹, ge, ge⁻¹, gx, gx⁻¹, gy, gy⁻¹, gc, gc⁻¹}

theorem baseSet_inv_mem : ∀ g ∈ baseSet, g⁻¹ ∈ baseSet := by
  intro g hg
  simp only [baseSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem of_mem_baseSet (i : Fin 6) : FreeGroup.of i ∈ baseSet := by
  fin_cases i <;> simp [baseSet, ga, gb, gd, ge, gx, gy]

theorem baseSet_closure_eq : Subgroup.closure baseSet = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  have hsub : Set.range (FreeGroup.of (α := Fin 6)) ⊆ baseSet := by
    rintro _ ⟨i, rfl⟩
    exact of_mem_baseSet i
  have h := Subgroup.closure_mono hsub
  rw [FreeGroup.closure_range_of] at h
  exact h (Subgroup.mem_top g)

/-- The relative generating set: the base letters and no peripheral subgroup. -/
def D : RelGenSet G Empty where
  base := baseSet
  fam := fun lam => lam.elim
  symmetricGenerating := by
    simpa [Set.iUnion_of_empty] using
      (⟨baseSet_inv_mem, baseSet_closure_eq⟩ : WordMetric.IsSymmetricGeneratingSet baseSet)

/-- The elements of word norm at most one. -/
def T : Set G := insert 1 baseSet

/-! ## Homomorphisms -/

def expD : G →* Multiplicative ℤ :=
  FreeGroup.lift fun i => if i = 2 then Multiplicative.ofAdd (1 : ℤ) else 1
def expE : G →* Multiplicative ℤ :=
  FreeGroup.lift fun i => if i = 3 then Multiplicative.ofAdd (1 : ℤ) else 1
def expA : G →* Multiplicative ℤ :=
  FreeGroup.lift fun i => if i = 0 then Multiplicative.ofAdd (1 : ℤ) else 1
def expB : G →* Multiplicative ℤ :=
  FreeGroup.lift fun i => if i = 1 then Multiplicative.ofAdd (1 : ℤ) else 1

/-- The 4-cycle `0 ↦ 1 ↦ 2 ↦ 3 ↦ 0`. -/
def sig : Equiv.Perm (Fin 4) where
  toFun := ![1, 2, 3, 0]
  invFun := ![3, 0, 1, 2]
  left_inv := by decide
  right_inv := by decide

/-- The transposition `0 ↔ 1`. -/
def tau : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide
  right_inv := by decide

/-- `a, b ↦ sig`, `x ↦ tau`, `d, e, y ↦ 1`. -/
def killP : G →* Equiv.Perm (Fin 4) := FreeGroup.lift ![sig, sig, 1, 1, tau, 1]
/-- `d, e ↦ sig`, `y ↦ tau`, `a, b, x ↦ 1`. -/
def killQ : G →* Equiv.Perm (Fin 4) := FreeGroup.lift ![1, 1, sig, sig, 1, tau]

@[simp] theorem expD_of (i : Fin 6) :
    expD (FreeGroup.of i) = if i = 2 then Multiplicative.ofAdd (1 : ℤ) else 1 :=
  FreeGroup.lift_apply_of
@[simp] theorem expE_of (i : Fin 6) :
    expE (FreeGroup.of i) = if i = 3 then Multiplicative.ofAdd (1 : ℤ) else 1 :=
  FreeGroup.lift_apply_of
@[simp] theorem expA_of (i : Fin 6) :
    expA (FreeGroup.of i) = if i = 0 then Multiplicative.ofAdd (1 : ℤ) else 1 :=
  FreeGroup.lift_apply_of
@[simp] theorem expB_of (i : Fin 6) :
    expB (FreeGroup.of i) = if i = 1 then Multiplicative.ofAdd (1 : ℤ) else 1 :=
  FreeGroup.lift_apply_of
@[simp] theorem killP_of (i : Fin 6) : killP (FreeGroup.of i) = ![sig, sig, 1, 1, tau, 1] i :=
  FreeGroup.lift_apply_of
@[simp] theorem killQ_of (i : Fin 6) : killQ (FreeGroup.of i) = ![1, 1, sig, sig, 1, tau] i :=
  FreeGroup.lift_apply_of

theorem killP_gc : killP gc = tau * (sig * sig * sig) * tau⁻¹ := by
  simp [gc, gP, gQ, ga, gb, gd, ge, gx, gy]

theorem killQ_gc : killQ gc = tau * (sig * sig * sig) * tau⁻¹ := by
  simp [gc, gP, gQ, ga, gb, gd, ge, gx, gy]

theorem killP_gQ : killP gQ = 1 := by simp [gQ, gd, ge]
theorem killQ_gP : killQ gP = 1 := by simp [gP, ga, gb]

theorem expD_gQ : Multiplicative.toAdd (expD gQ) = 2 := by
  simp [gQ, gd, ge]; rfl
theorem expE_gQ : Multiplicative.toAdd (expE gQ) = 1 := by
  simp [gQ, gd, ge]; rfl
theorem expA_gP : Multiplicative.toAdd (expA gP) = 2 := by
  simp [gP, ga, gb]; rfl
theorem expB_gP : Multiplicative.toAdd (expB gP) = 1 := by
  simp [gP, ga, gb]; rfl

theorem tau_inv : tau⁻¹ = tau := by decide

theorem expD_conj (g r : G) : expD (g * r * g⁻¹) = expD r := by
  rw [map_mul, map_mul, map_inv]; exact mul_inv_cancel_comm _ _
theorem expE_conj (g r : G) : expE (g * r * g⁻¹) = expE r := by
  rw [map_mul, map_mul, map_inv]; exact mul_inv_cancel_comm _ _
theorem expA_conj (g r : G) : expA (g * r * g⁻¹) = expA r := by
  rw [map_mul, map_mul, map_inv]; exact mul_inv_cancel_comm _ _
theorem expB_conj (g r : G) : expB (g * r * g⁻¹) = expB r := by
  rw [map_mul, map_mul, map_inv]; exact mul_inv_cancel_comm _ _

/-! ## Words over two letters -/

theorem listVal_cons (l : RelLetter G Empty) (w : List (RelLetter G Empty)) :
    RelLetter.listVal (l :: w) = l.val * RelLetter.listVal w := by
  simp [RelLetter.listVal]

/-- A word over `a, b` has kill image `sig ^ length` and no `d, e` exponent. -/
theorem killP_listVal_ab : ∀ w : List (RelLetter G Empty),
    (∀ l ∈ w, l = .base ga ∨ l = .base gb) →
      killP (RelLetter.listVal w) = sig ^ w.length ∧ expD (RelLetter.listVal w) = 1 ∧
        expE (RelLetter.listVal w) = 1
  | [], _ => by simp [RelLetter.listVal]
  | l :: w, h => by
    obtain ⟨ih₁, ih₂, ih₃⟩ := killP_listVal_ab w fun l' hl' => h l' (by simp [hl'])
    rw [listVal_cons]
    rcases h l (by simp) with rfl | rfl <;>
      simp [ih₁, ih₂, ih₃, RelLetter.val, ga, gb, pow_succ']

/-- A word over `d, e` has kill image `sig ^ length` and no `a, b` exponent. -/
theorem killQ_listVal_de : ∀ w : List (RelLetter G Empty),
    (∀ l ∈ w, l = .base gd ∨ l = .base ge) →
      killQ (RelLetter.listVal w) = sig ^ w.length ∧ expA (RelLetter.listVal w) = 1 ∧
        expB (RelLetter.listVal w) = 1
  | [], _ => by simp [RelLetter.listVal]
  | l :: w, h => by
    obtain ⟨ih₁, ih₂, ih₃⟩ := killQ_listVal_de w fun l' hl' => h l' (by simp [hl'])
    rw [listVal_cons]
    rcases h l (by simp) with rfl | rfl <;>
      simp [ih₁, ih₂, ih₃, RelLetter.val, gd, ge, pow_succ']

theorem mem_pWord_arc {m n : ℕ} : ∀ l ∈ (pWord.rotate m).take n, l = .base ga ∨ l = .base gb := by
  intro l hl
  have h := List.mem_rotate.mp (List.mem_of_mem_take hl)
  simp only [pWord, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp

theorem mem_qWord_arc {m n : ℕ} : ∀ l ∈ (qWord.rotate m).take n, l = .base gd ∨ l = .base ge := by
  intro l hl
  have h := List.mem_rotate.mp (List.mem_of_mem_take hl)
  simp only [qWord, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp

theorem length_pWord_arc {m n : ℕ} (hn : n < 3) : ((pWord.rotate m).take n).length = n := by
  simp [pWord]; omega

theorem length_qWord_arc {m n : ℕ} (hn : n < 3) : ((qWord.rotate m).take n).length = n := by
  simp [qWord]; omega

/-! ## Letters of word norm at most one -/

/-- A letter of norm at most one is `c`, `c⁻¹`, or has kill image among `1, sig, sig⁻¹, tau` and at
most one unit `d, e` exponent. -/
theorem letter_casesP {β : G} (hβ : β ∈ T) :
    β = gc ∨ β = gc⁻¹ ∨
      ((killP β = 1 ∨ killP β = sig ∨ killP β = sig⁻¹ ∨ killP β = tau) ∧
        ((Multiplicative.toAdd (expD β) = 0 ∧ Multiplicative.toAdd (expE β) = 0) ∨
          (Multiplicative.toAdd (expD β) = 1 ∧ Multiplicative.toAdd (expE β) = 0) ∨
          (Multiplicative.toAdd (expD β) = -1 ∧ Multiplicative.toAdd (expE β) = 0) ∨
          (Multiplicative.toAdd (expD β) = 0 ∧ Multiplicative.toAdd (expE β) = 1) ∨
          (Multiplicative.toAdd (expD β) = 0 ∧ Multiplicative.toAdd (expE β) = -1))) := by
  simp only [T, baseSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
  rcases hβ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr ⟨by simp [ga, gb, gd, ge, gx, gy, tau_inv], by
        simp [ga, gb, gd, ge, gx, gy]⟩)

/-- The same for the kept word `P`: kill image through `killQ`, exponents over `a, b`. -/
theorem letter_casesQ {β : G} (hβ : β ∈ T) :
    β = gc ∨ β = gc⁻¹ ∨
      ((killQ β = 1 ∨ killQ β = sig ∨ killQ β = sig⁻¹ ∨ killQ β = tau) ∧
        ((Multiplicative.toAdd (expA β) = 0 ∧ Multiplicative.toAdd (expB β) = 0) ∨
          (Multiplicative.toAdd (expA β) = 1 ∧ Multiplicative.toAdd (expB β) = 0) ∨
          (Multiplicative.toAdd (expA β) = -1 ∧ Multiplicative.toAdd (expB β) = 0) ∨
          (Multiplicative.toAdd (expA β) = 0 ∧ Multiplicative.toAdd (expB β) = 1) ∨
          (Multiplicative.toAdd (expA β) = 0 ∧ Multiplicative.toAdd (expB β) = -1))) := by
  simp only [T, baseSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
  rcases hβ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr ⟨by simp [ga, gb, gd, ge, gx, gy, tau_inv], by
        simp [ga, gb, gd, ge, gx, gy]⟩)

end GroupApproximation.GGT.VanKampen.OsinPocketPinchPosModels

#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketPinchPosModels.D
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketPinchPosModels.killP_gc
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketPinchPosModels.expD_gQ
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketPinchPosModels.killP_listVal_ab
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketPinchPosModels.letter_casesP
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketPinchPosModels.letter_casesQ
