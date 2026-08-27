import GroupApproximation.Steinberg.A2System
import GroupApproximation.Leavitt.MatrixSelfSimilarity
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

namespace GroupApproximation
namespace SteinbergBlockRoot

open SteinbergGroup
open scoped BigOperators commutatorElement

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

/-- A commutator with a commuting product is the corresponding commuting
product of elementary commutators when all source factors commute with all
result factors. -/
theorem noncommProd_commutator_right
    {G α : Type*} [Group G] (s : Finset α) (f w : α → G)
    (hf : (s : Set α).Pairwise (Function.onFun Commute f))
    (hw : (s : Set α).Pairwise (Function.onFun Commute w))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, Commute (f i) (w j))
    (c : G) (hbase : ∀ i ∈ s, ⁅f i, c⁆ = w i) :
    ⁅s.noncommProd f hf, c⁆ = s.noncommProd w hw := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.noncommProd_cons, Finset.noncommProd_cons,
        commutatorElement_mul_left_eq_conj_mul]
      rw [ih
        (hf.mono fun _ ↦ Finset.mem_cons.2 ∘ .inr)
        (hw.mono fun _ ↦ Finset.mem_cons.2 ∘ .inr)
        (fun i hi j hj ↦ hcross i (Finset.mem_cons_of_mem hi)
          j (Finset.mem_cons_of_mem hj))
        (fun i hi ↦ hbase i (Finset.mem_cons_of_mem hi)),
        hbase a (Finset.mem_cons_self a s)]
      have hcomm : Commute (f a)
          (s.noncommProd w
            (hw.mono fun _ ↦ Finset.mem_cons.2 ∘ .inr)) :=
        Finset.noncommProd_commute s w
          (hw.mono fun _ ↦ Finset.mem_cons.2 ∘ .inr) (f a)
          (fun j hj ↦ hcross a (Finset.mem_cons_self a s)
            j (Finset.mem_cons_of_mem hj))
      rw [hcomm.mul_inv_cancel]
      exact (Finset.noncommProd_commute s w
        (hw.mono fun _ ↦ Finset.mem_cons.2 ∘ .inr) (w a)
        (fun j hj ↦ hw.of_refl (Finset.mem_cons_self a s)
          (Finset.mem_cons_of_mem hj))).eq.symm

/-- The commutator of two commuting products whose only nontrivial
cross-commutators occur at matching indices is the product of those diagonal
commutators. -/
theorem noncommProd_commutator_diagonal
    {G α : Type*} [Group G] (s : Finset α) (f g w : α → G)
    (hf : (s : Set α).Pairwise (Function.onFun Commute f))
    (hg : (s : Set α).Pairwise (Function.onFun Commute g))
    (hw : (s : Set α).Pairwise (Function.onFun Commute w))
    (hfw : ∀ i ∈ s, ∀ j ∈ s, Commute (f i) (w j))
    (hdiag : ∀ i ∈ s, ⁅f i, g i⁆ = w i)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Commute (f i) (g j)) :
    ⁅s.noncommProd f hf, s.noncommProd g hg⁆ =
      s.noncommProd w hw := by
  classical
  apply noncommProd_commutator_right s f w hf hw hfw
  intro i hi
  rw [← Finset.mul_noncommProd_erase s hi g hg,
    commutatorElement_mul_right_eq_mul_conj, hdiag i hi]
  have hrest : Commute (f i)
      ((s.erase i).noncommProd g fun _ hj _ hk hjk ↦
        hg (Finset.mem_of_mem_erase hj) (Finset.mem_of_mem_erase hk) hjk) :=
    Finset.noncommProd_commute (s.erase i) g _ (f i) fun j hj ↦
      hoff i hi j (Finset.mem_of_mem_erase hj)
        (Finset.ne_of_mem_erase hj).symm
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hrest.eq]
  simp

/-- A finite family contained in one Steinberg root subgroup commutes
pairwise. -/
theorem x_pairwise (s : Finset κ) (i j : Fin 2 ⊕ κ) (hij : i ≠ j)
    (c : κ → R) :
    (s : Set κ).Pairwise
      (Function.onFun Commute fun k ↦ x i j hij (c k)) := by
  intro k _ l _ _
  change Commute (x i j hij (c k)) (x i j hij (c l))
  rw [commute_iff_eq, x_mul, x_mul, add_comm]

/-- A commuting product in one Steinberg root subgroup is the root element
whose coefficient is the corresponding sum. -/
theorem x_noncommProd (s : Finset κ) (i j : Fin 2 ⊕ κ) (hij : i ≠ j)
    (c : κ → R) :
    s.noncommProd (fun k ↦ x i j hij (c k)) (x_pairwise s i j hij c) =
      x i j hij (∑ k ∈ s, c k) := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons k s hk ih =>
      rw [Finset.noncommProd_cons, ih, Finset.sum_cons hk, x_mul]

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

/-- Multiplication by one right-family element extracts the corresponding
ordinary singleton-to-tail root. -/
theorem rowToTail_mul_right (F : CompleteMatrixFamily R κ)
    (p : Fin 2) (j : κ) (a : R) :
    rowToTail F p (a * F.right j) =
      x (Sum.inl p) (Sum.inr j) (by simp) a := by
  classical
  unfold rowToTail
  rw [← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ j)]
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1]
  · simp [mul_assoc, F.orthogonal]
  · intro k hk
    rw [show (a * F.right j) * F.left k = 0 by
      simp [mul_assoc, F.orthogonal,
        (Finset.ne_of_mem_erase hk).symm]]
    exact x_zero _ _ _

/-- Multiplication by one left-family element extracts the corresponding
ordinary tail-to-singleton root. -/
theorem tailToRow_mul_left (F : CompleteMatrixFamily R κ)
    (p : Fin 2) (i : κ) (a : R) :
    tailToRow F p (F.left i * a) =
      x (Sum.inr i) (Sum.inl p) (by simp) a := by
  classical
  unfold tailToRow
  rw [← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i)]
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1]
  · rw [one_pow, mul_one]
    congr 1
    calc
      F.right i * (F.left i * a) = (F.right i * F.left i) * a :=
        (mul_assoc _ _ _).symm
      _ = a := by rw [F.orthogonal i i]; simp
  · intro k hk
    rw [show F.right k * (F.left i * a) = 0 by
      simp [← mul_assoc, F.orthogonal, Finset.ne_of_mem_erase hk]]
    exact x_zero _ _ _

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

/-- A singleton root commutes with a singleton-to-tail root having the same
source singleton. -/
theorem smallRoot_rowToTail_commute (F : CompleteMatrixFamily R κ)
    (p q : Fin 2) (hpq : p ≠ q) (a b : R) :
    Commute (smallRoot (κ := κ) p q hpq a) (rowToTail F p b) := by
  unfold smallRoot rowToTail
  exact Finset.noncommProd_commute Finset.univ _
    (rowToTail_pairwise F p b) _ fun j _ ↦
      x_commute_of_ne _ _ _ _ (by simpa using hpq) (by simp)
        (by simpa using hpq.symm) (by simp) _ _

/-- A tail-to-singleton root commutes with a singleton root having the same
target singleton. -/
theorem tailToRow_smallRoot_commute (F : CompleteMatrixFamily R κ)
    (p q : Fin 2) (hpq : p ≠ q) (a b : R) :
    Commute (tailToRow F q a) (smallRoot (κ := κ) p q hpq b) := by
  unfold smallRoot tailToRow
  exact (Finset.noncommProd_commute Finset.univ _
    (tailToRow_pairwise F q a) _ fun i _ ↦
      x_commute_of_ne (Sum.inl p) (Sum.inl q) (Sum.inr i) (Sum.inl q)
        (by simpa using hpq) (by simp) (by simp)
        (by simpa using hpq.symm) _ _).symm

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

/-- The adjacent commutator of a rectangular tail-to-singleton root with
an ordinary singleton root. -/
theorem tailToRow_smallRoot_commutator (F : CompleteMatrixFamily R κ)
    (p q : Fin 2) (hpq : p ≠ q) (a b : R) :
    ⁅tailToRow F p a, smallRoot (κ := κ) p q hpq b⁆ =
      tailToRow F q (a * b) := by
  classical
  unfold tailToRow smallRoot
  apply noncommProd_commutator_right
  · intro i _ j _
    exact x_commute_of_ne _ _ _ _ (by simp) (by simp)
      (by simp) (by simp) _ _
  · intro i _
    rw [x_commutator (Sum.inr i) (Sum.inl p) (Sum.inl q)
      (by simp) (by simpa using hpq) (by simp)]
    congr 1
    exact mul_assoc _ _ _

/-- The commutator of the two rectangular roots through the tail block is
the ordinary root between the singleton blocks.  The coefficient calculation
is exactly the completeness relation `∑ i, F.left i * F.right i = 1`. -/
theorem rowToTail_tailToRow_commutator (F : CompleteMatrixFamily R κ)
    (p q : Fin 2) (hpq : p ≠ q) (a b : R) :
    ⁅rowToTail F p a, tailToRow F q b⁆ =
      smallRoot (κ := κ) p q hpq (a * b) := by
  classical
  let f : κ → SteinbergGroup (Fin 2 ⊕ κ) R := fun i ↦
    x (Sum.inl p) (Sum.inr i) (by simp) (a * F.left i)
  let g : κ → SteinbergGroup (Fin 2 ⊕ κ) R := fun i ↦
    x (Sum.inr i) (Sum.inl q) (by simp) (F.right i * b)
  let w : κ → SteinbergGroup (Fin 2 ⊕ κ) R := fun i ↦
    x (Sum.inl p) (Sum.inl q) (by simpa) ((a * F.left i) * (F.right i * b))
  have hdiag : ⁅(Finset.univ.noncommProd f (rowToTail_pairwise F p a)),
      (Finset.univ.noncommProd g (tailToRow_pairwise F q b))⁆ =
      Finset.univ.noncommProd w
        (x_pairwise Finset.univ (Sum.inl p) (Sum.inl q) (by simpa) fun i ↦
          (a * F.left i) * (F.right i * b)) := by
    apply noncommProd_commutator_diagonal
    · intro i _ j _
      dsimp only [f, w]
      exact x_commute_of_ne _ _ _ _ (by simp) (by simpa using hpq)
        (by simp) (by simpa using hpq.symm) _ _
    · intro i _
      dsimp only [f, g, w]
      exact x_commutator (Sum.inl p) (Sum.inr i) (Sum.inl q)
        (by simp) (by simp) (by simpa using hpq) _ _
    · intro i _ j _ hij
      dsimp only [f, g]
      exact x_commute_of_ne _ _ _ _ (by simp) (by simp)
        (by simpa using hij) (by simpa using hpq.symm) _ _
  change ⁅Finset.univ.noncommProd f (rowToTail_pairwise F p a),
      Finset.univ.noncommProd g (tailToRow_pairwise F q b)⁆ = _
  rw [hdiag]
  rw [x_noncommProd]
  unfold smallRoot
  congr 1
  calc
    (∑ i, (a * F.left i) * (F.right i * b)) =
        (∑ i, a * (F.left i * F.right i)) * b := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_assoc]
    _ = (a * ∑ i, F.left i * F.right i) * b := by
      rw [Finset.mul_sum]
    _ = a * b := by rw [F.complete]; simp

end SteinbergBlockRoot
end GroupApproximation
