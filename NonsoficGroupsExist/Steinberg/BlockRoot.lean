import NonsoficGroupsExist.Steinberg.A2System
import NonsoficGroupsExist.Leavitt.MatrixSelfSimilarity
import Mathlib.Data.Finset.NoncommProd

/-!
# Rectangular Steinberg root products

A complete matrix family identifies one free rank-one module with a finite
free module.  This file begins the corresponding construction inside a
Steinberg presentation.  With index type `Fin 2 ⊕ κ`, the first two indices
are singleton blocks and `κ` is the finite tail block.  Products of roots
from a singleton block to the tail, and in the reverse direction, are
defined using `Finset.noncommProd`; the Steinberg commutation relations make
those products canonical.

The additive laws proved here are the first algebraic input for the
three-block `A₂` quotient that transports rank-three property `(T)` to an
arbitrary finite Leavitt rank.
-/

namespace NonsoficGroupsExist
namespace SteinbergBlockRoot

open SteinbergGroup
open scoped commutatorElement

variable {R κ : Type*} [Ring R] [Fintype κ] [DecidableEq κ]

/-- Products of two finite commuting families commute if every cross pair
commutes. -/
theorem commute_noncommProd_noncommProd
    {G α β : Type*} [Group G]
    (s : Finset α) (t : Finset β) (f : α → G) (g : β → G)
    (hf : (s : Set α).Pairwise (Function.onFun Commute f))
    (hg : (t : Set β).Pairwise (Function.onFun Commute g))
    (hcross : ∀ i ∈ s, ∀ j ∈ t, Commute (f i) (g j)) :
    Commute (s.noncommProd f hf) (t.noncommProd g hg) := by
  apply (Finset.noncommProd_commute s f hf
    (t.noncommProd g hg) fun i hi ↦ ?_).symm
  exact (Finset.noncommProd_commute t g hg (f i)
    (fun j hj ↦ hcross i hi j hj)).symm

/-- The roots from singleton block `p` to the tail commute pairwise. -/
theorem rowToTail_pairwise (F : CompleteMatrixFamily R κ)
    (p : Fin 2) (a : R) :
    ((Finset.univ : Finset κ) : Set κ).Pairwise
      (Function.onFun Commute fun j ↦
        x (Sum.inl p) (Sum.inr j) (by simp) (a * F.left j)) := by
  intro j _ k _ hjk
  exact x_commute_of_ne _ _ _ _ (by simp) (by simp)
    (by simp) (by simp) _ _

/-- The roots from the tail to singleton block `p` commute pairwise. -/
theorem tailToRow_pairwise (F : CompleteMatrixFamily R κ)
    (p : Fin 2) (a : R) :
    ((Finset.univ : Finset κ) : Set κ).Pairwise
      (Function.onFun Commute fun i ↦
        x (Sum.inr i) (Sum.inl p) (by simp) (F.right i * a)) := by
  intro i _ j _ hij
  exact x_commute_of_ne _ _ _ _ (by simp) (by simp)
    (by simp) (by simp) _ _

/-- A rectangular Steinberg root from singleton block `p` to the tail. -/
def rowToTail (F : CompleteMatrixFamily R κ) (p : Fin 2) (a : R) :
    SteinbergGroup (Fin 2 ⊕ κ) R :=
  Finset.univ.noncommProd
    (fun j ↦ x (Sum.inl p) (Sum.inr j) (by simp) (a * F.left j))
    (rowToTail_pairwise F p a)

/-- A rectangular Steinberg root from the tail to singleton block `p`. -/
def tailToRow (F : CompleteMatrixFamily R κ) (p : Fin 2) (a : R) :
    SteinbergGroup (Fin 2 ⊕ κ) R :=
  Finset.univ.noncommProd
    (fun i ↦ x (Sum.inr i) (Sum.inl p) (by simp) (F.right i * a))
    (tailToRow_pairwise F p a)

@[simp] theorem rowToTail_zero (F : CompleteMatrixFamily R κ) (p : Fin 2) :
    rowToTail F p 0 = 1 := by
  unfold rowToTail
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1]
  · exact one_pow _
  · intro j _
    simp [x_zero]

@[simp] theorem tailToRow_zero (F : CompleteMatrixFamily R κ) (p : Fin 2) :
    tailToRow F p 0 = 1 := by
  unfold tailToRow
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1]
  · exact one_pow _
  · intro i _
    simp [x_zero]

/-- Additivity of a singleton-to-tail rectangular root. -/
theorem rowToTail_add (F : CompleteMatrixFamily R κ) (p : Fin 2)
    (a b : R) : rowToTail F p (a + b) = rowToTail F p a * rowToTail F p b := by
  unfold rowToTail
  rw [← Finset.noncommProd_mul_distrib
    (fun j : κ ↦ x (Sum.inl p) (Sum.inr j) (by simp) (a * F.left j))
    (fun j : κ ↦ x (Sum.inl p) (Sum.inr j) (by simp) (b * F.left j))
    (rowToTail_pairwise F p a) (rowToTail_pairwise F p b)]
  · apply Finset.noncommProd_congr rfl
    intro j _
    dsimp only [Pi.mul_apply]
    rw [add_mul, x_mul]
  · intro i _ j _ hij
    exact x_commute_of_ne _ _ _ _ (by simp) (by simp)
      (by simp) (by simp) _ _

/-- Additivity of a tail-to-singleton rectangular root. -/
theorem tailToRow_add (F : CompleteMatrixFamily R κ) (p : Fin 2)
    (a b : R) : tailToRow F p (a + b) = tailToRow F p a * tailToRow F p b := by
  unfold tailToRow
  rw [← Finset.noncommProd_mul_distrib
    (fun i : κ ↦ x (Sum.inr i) (Sum.inl p) (by simp) (F.right i * a))
    (fun i : κ ↦ x (Sum.inr i) (Sum.inl p) (by simp) (F.right i * b))
    (tailToRow_pairwise F p a) (tailToRow_pairwise F p b)]
  · apply Finset.noncommProd_congr rfl
    intro i _
    dsimp only [Pi.mul_apply]
    rw [mul_add, x_mul]
  · intro i _ j _ hij
    exact x_commute_of_ne _ _ _ _ (by simp) (by simp)
      (by simp) (by simp) _ _

/-- Two singleton-to-tail rectangular roots commute. -/
theorem rowToTail_commute (F : CompleteMatrixFamily R κ)
    (p q : Fin 2) (a b : R) : Commute (rowToTail F p a) (rowToTail F q b) := by
  unfold rowToTail
  exact commute_noncommProd_noncommProd
    (Finset.univ : Finset κ) (Finset.univ : Finset κ) _ _
    (rowToTail_pairwise F p a) (rowToTail_pairwise F q b) (by
      intro i _ j _
      exact x_commute_of_ne _ _ _ _ (by simp) (by simp)
        (by simp) (by simp) _ _)

/-- Two tail-to-singleton rectangular roots commute. -/
theorem tailToRow_commute (F : CompleteMatrixFamily R κ)
    (p q : Fin 2) (a b : R) : Commute (tailToRow F p a) (tailToRow F q b) := by
  unfold tailToRow
  exact commute_noncommProd_noncommProd
    (Finset.univ : Finset κ) (Finset.univ : Finset κ) _ _
    (tailToRow_pairwise F p a) (tailToRow_pairwise F q b) (by
      intro i _ j _
      exact x_commute_of_ne _ _ _ _ (by simp) (by simp)
        (by simp) (by simp) _ _)

@[simp] theorem rowToTail_neg (F : CompleteMatrixFamily R κ)
    (p : Fin 2) (a : R) : rowToTail F p (-a) = (rowToTail F p a)⁻¹ := by
  apply mul_left_cancel (a := rowToTail F p a)
  rw [← rowToTail_add]
  simp

@[simp] theorem tailToRow_neg (F : CompleteMatrixFamily R κ)
    (p : Fin 2) (a : R) : tailToRow F p (-a) = (tailToRow F p a)⁻¹ := by
  apply mul_left_cancel (a := tailToRow F p a)
  rw [← tailToRow_add]
  simp

/-- The additive rectangular root subgroup from singleton block `p` to the
tail. -/
def rowToTailSubgroup (F : CompleteMatrixFamily R κ) (p : Fin 2) :
    Subgroup (SteinbergGroup (Fin 2 ⊕ κ) R) where
  carrier := Set.range (rowToTail F p)
  one_mem' := ⟨0, rowToTail_zero F p⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, rowToTail_add F p a b⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, rowToTail_neg F p a⟩

/-- The additive rectangular root subgroup from the tail to singleton block
`p`. -/
def tailToRowSubgroup (F : CompleteMatrixFamily R κ) (p : Fin 2) :
    Subgroup (SteinbergGroup (Fin 2 ⊕ κ) R) where
  carrier := Set.range (tailToRow F p)
  one_mem' := ⟨0, tailToRow_zero F p⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, tailToRow_add F p a b⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, tailToRow_neg F p a⟩

/-- An ordinary root between the two singleton blocks. -/
def smallRoot (p q : Fin 2) (hpq : p ≠ q) (a : R) :
    SteinbergGroup (Fin 2 ⊕ κ) R :=
  x (Sum.inl p) (Sum.inl q) (by simpa) a

/-- The adjacent commutator of a singleton root with a rectangular
singleton-to-tail root. -/
theorem smallRoot_rowToTail_commutator (F : CompleteMatrixFamily R κ)
    (p q : Fin 2) (hpq : p ≠ q) (a b : R) :
    ⁅smallRoot (κ := κ) p q hpq a, rowToTail F q b⁆ =
      rowToTail F p (a * b) := by
  classical
  let u : SteinbergGroup (Fin 2 ⊕ κ) R := smallRoot p q hpq a
  let v : κ → SteinbergGroup (Fin 2 ⊕ κ) R := fun j ↦
    x (Sum.inl q) (Sum.inr j) (by simp) (b * F.left j)
  let w : κ → SteinbergGroup (Fin 2 ⊕ κ) R := fun j ↦
    x (Sum.inl p) (Sum.inr j) (by simp) ((a * b) * F.left j)
  apply mul_right_cancel (b := rowToTail F q b)
  rw [← conj_eq_commutatorElement_mul]
  change MulAut.conj u
      (Finset.univ.noncommProd v (rowToTail_pairwise F q b)) =
    Finset.univ.noncommProd w (rowToTail_pairwise F p (a * b)) *
      Finset.univ.noncommProd v (rowToTail_pairwise F q b)
  rw [Finset.map_noncommProd]
  have hconj : (fun j ↦ MulAut.conj u (v j)) = fun j ↦ w j * v j := by
    funext j
    dsimp only [u, v, w, smallRoot]
    rw [conj_eq_commutatorElement_mul,
      x_commutator (Sum.inl p) (Sum.inl q) (Sum.inr j)
        (by simpa using hpq) (by simp) (by simp)]
    congr 2
    simp only [mul_assoc]
  have hcross : ((Finset.univ : Finset κ) : Set κ).Pairwise
      fun i j ↦ Commute (v i) (w j) := by
    intro i _ j _ hij
    dsimp only [v, w]
    exact x_commute_of_ne _ _ _ _ (by simp) (by simp)
      (by simp) (by simp) _ _
  rw [← Finset.noncommProd_mul_distrib
    w v (rowToTail_pairwise F p (a * b))
      (rowToTail_pairwise F q b) hcross]
  apply Finset.noncommProd_congr rfl
  intro j _
  exact congrFun hconj j

end SteinbergBlockRoot
end NonsoficGroupsExist
