import GroupApproximation.Steinberg.BlockRoot

/-!
# The three-block `A₂` system

The two singleton blocks and one finite tail block define six additive root
subgroups inside a higher-rank Steinberg group.  This file packages those
subgroups and proves that they generate the ambient group.
-/

namespace GroupApproximation
namespace SteinbergBlockRoot

open SteinbergGroup
open scoped commutatorElement

variable {R κ : Type*} [Ring R] [Fintype κ] [DecidableEq κ]

/-- The ordinary root subgroup between the two singleton blocks. -/
def smallRootSubgroup (p q : Fin 2) (hpq : p ≠ q) :
    Subgroup (SteinbergGroup (Fin 2 ⊕ κ) R) :=
  rootSubgroup (Sum.inl p) (Sum.inl q) (by simpa)

/-- Regard a non-tail block index as one of the two singleton indices. -/
def singletonOfNotTail (i : Fin 3) (hi : i ≠ 2) : Fin 2 :=
  ⟨i, by omega⟩

theorem singletonOfNotTail_ne (i j : Fin 3) (hi : i ≠ 2) (hj : j ≠ 2)
    (hij : i ≠ j) : singletonOfNotTail i hi ≠ singletonOfNotTail j hj :=
  fun h ↦ hij (Fin.ext (by
    simpa [singletonOfNotTail] using
      congrArg (fun p : Fin 2 ↦ p.val) h))

/-- The six root subgroups associated to the block decomposition
`1 + 1 + |κ|`. -/
def blockRootSubgroup (F : CompleteMatrixFamily R κ)
    (i j : Fin 3) (hij : i ≠ j) :
    Subgroup (SteinbergGroup (Fin 2 ⊕ κ) R) :=
  if hi : i = 2 then
    tailToRowSubgroup F (singletonOfNotTail j fun hj ↦
      hij (hi.trans hj.symm))
  else if hj : j = 2 then
    rowToTailSubgroup F (singletonOfNotTail i hi)
  else
    smallRootSubgroup (singletonOfNotTail i hi) (singletonOfNotTail j hj)
      fun hpq ↦ hij (Fin.ext (by
        simpa [singletonOfNotTail] using
          congrArg (fun p : Fin 2 ↦ p.val) hpq))

/-- The union of the six block root subgroups. -/
def blockRootSet (F : CompleteMatrixFamily R κ) :
    Set (SteinbergGroup (Fin 2 ⊕ κ) R) :=
  {g | ∃ (i j : Fin 3) (hij : i ≠ j),
    g ∈ blockRootSubgroup F i j hij}

theorem rowToTail_mem_blockRootSet (F : CompleteMatrixFamily R κ)
    (p : Fin 2) (a : R) : rowToTail F p a ∈ blockRootSet F := by
  fin_cases p
  · exact ⟨0, 2, by decide, by simpa [blockRootSubgroup, singletonOfNotTail] using
      (show rowToTail F 0 a ∈ rowToTailSubgroup F 0 from ⟨a, rfl⟩)⟩
  · exact ⟨1, 2, by decide, by simpa [blockRootSubgroup, singletonOfNotTail] using
      (show rowToTail F 1 a ∈ rowToTailSubgroup F 1 from ⟨a, rfl⟩)⟩

theorem tailToRow_mem_blockRootSet (F : CompleteMatrixFamily R κ)
    (p : Fin 2) (a : R) : tailToRow F p a ∈ blockRootSet F := by
  fin_cases p
  · exact ⟨2, 0, by decide, by simpa [blockRootSubgroup, singletonOfNotTail] using
      (show tailToRow F 0 a ∈ tailToRowSubgroup F 0 from ⟨a, rfl⟩)⟩
  · exact ⟨2, 1, by decide, by simpa [blockRootSubgroup, singletonOfNotTail] using
      (show tailToRow F 1 a ∈ tailToRowSubgroup F 1 from ⟨a, rfl⟩)⟩

theorem smallRoot_mem_blockRootSet (F : CompleteMatrixFamily R κ)
    (p q : Fin 2) (hpq : p ≠ q) (a : R) :
    smallRoot (κ := κ) p q hpq a ∈ blockRootSet F := by
  fin_cases p <;> fin_cases q
  · exact (hpq rfl).elim
  · exact ⟨0, 1, by decide, by simpa [blockRootSubgroup, singletonOfNotTail,
      smallRootSubgroup] using
        (show smallRoot (κ := κ) 0 1 (by decide) a ∈
          smallRootSubgroup (κ := κ) 0 1 (by decide) from ⟨a, rfl⟩)⟩
  · exact ⟨1, 0, by decide, by simpa [blockRootSubgroup, singletonOfNotTail,
      smallRootSubgroup] using
        (show smallRoot (κ := κ) 1 0 (by decide) a ∈
          smallRootSubgroup (κ := κ) 1 0 (by decide) from ⟨a, rfl⟩)⟩
  · exact (hpq rfl).elim

/-- The six block roots generate every ordinary Steinberg root, including
roots internal to the tail (as commutators through the first singleton). -/
theorem blockRootSet_generate (F : CompleteMatrixFamily R κ) :
    Subgroup.closure (blockRootSet F) = ⊤ := by
  let H := Subgroup.closure (blockRootSet F)
  have hrow (p : Fin 2) (a : R) : rowToTail F p a ∈ H :=
    Subgroup.subset_closure (rowToTail_mem_blockRootSet F p a)
  have htail (p : Fin 2) (a : R) : tailToRow F p a ∈ H :=
    Subgroup.subset_closure (tailToRow_mem_blockRootSet F p a)
  have hsmall (p q : Fin 2) (hpq : p ≠ q) (a : R) :
      smallRoot (κ := κ) p q hpq a ∈ H :=
    Subgroup.subset_closure (smallRoot_mem_blockRootSet F p q hpq a)
  have hrowOrdinary (p : Fin 2) (j : κ) (a : R) :
      x (Sum.inl p) (Sum.inr j) (by simp) a ∈ H := by
    rw [← rowToTail_mul_right F p j a]
    exact hrow p (a * F.right j)
  have htailOrdinary (p : Fin 2) (i : κ) (a : R) :
      x (Sum.inr i) (Sum.inl p) (by simp) a ∈ H := by
    rw [← tailToRow_mul_left F p i a]
    exact htail p (F.left i * a)
  apply top_unique
  rw [← rootSet_generate (I := Fin 2 ⊕ κ) (R := R)]
  rw [Subgroup.closure_le]
  rintro z ⟨u, v, huv, a, rfl⟩
  rcases u with p | i <;> rcases v with q | j
  · have hpq : p ≠ q := fun h ↦ huv (congrArg Sum.inl h)
    simpa [smallRoot] using hsmall p q hpq a
  · exact hrowOrdinary p j a
  · exact htailOrdinary q i a
  · have hij : i ≠ j := fun h ↦ huv (congrArg Sum.inr h)
    have hu : x (Sum.inr i) (Sum.inl (0 : Fin 2)) (by simp) a ∈ H :=
      htailOrdinary 0 i a
    have hv : x (Sum.inl (0 : Fin 2)) (Sum.inr j) (by simp) 1 ∈ H :=
      hrowOrdinary 0 j 1
    have hc : ⁅x (Sum.inr i) (Sum.inl (0 : Fin 2)) (by simp) a,
        x (Sum.inl (0 : Fin 2)) (Sum.inr j) (by simp) 1⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hu hv) (H.inv_mem hu))
        (H.inv_mem hv)
    rw [x_commutator (Sum.inr i) (Sum.inl (0 : Fin 2)) (Sum.inr j)
      (by simp) (by simp) (by simpa using hij)] at hc
    simpa using hc

theorem blockRoot_commute (F : CompleteMatrixFamily R κ) :
    ∀ (i j k l : Fin 3) (hij : i ≠ j) (hkl : k ≠ l),
      j ≠ k → l ≠ i →
      ∀ x ∈ blockRootSubgroup F i j hij,
        ∀ y ∈ blockRootSubgroup F k l hkl, Commute x y := by
  intro i j k l hij hkl hjk hli x hx y hy
  by_cases hi : i = 2
  · subst i
    have hj : j ≠ 2 := by omega
    by_cases hk : k = 2
    · subst k
      have hl : l ≠ 2 := by omega
      simp [blockRootSubgroup, singletonOfNotTail] at hx hy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact tailToRow_commute F _ _ _ _
    · have hl : l ≠ 2 := by omega
      have hlj : l = j := by omega
      subst l
      simp [blockRootSubgroup, singletonOfNotTail, smallRootSubgroup,
        hk, hj] at hx hy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact tailToRow_smallRoot_commute F _ _
        (singletonOfNotTail_ne k j hk hj hkl) _ _
  · by_cases hj : j = 2
    · subst j
      have hk : k ≠ 2 := by omega
      by_cases hl : l = 2
      · subst l
        simp [blockRootSubgroup, singletonOfNotTail, hi, hk] at hx hy
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact rowToTail_commute F _ _ _ _
      · have hki : k = i := by omega
        subst k
        simp [blockRootSubgroup, singletonOfNotTail, smallRootSubgroup,
          hi, hl] at hx hy
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact (smallRoot_rowToTail_commute F _ _
          (singletonOfNotTail_ne i l hi hl hkl) b a).symm
    · by_cases hk : k = 2
      · subst k
        have hl : l ≠ 2 := by omega
        have hlj : l = j := by omega
        subst l
        simp [blockRootSubgroup, singletonOfNotTail, smallRootSubgroup,
          hi, hj] at hx hy
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact (tailToRow_smallRoot_commute F _ _
          (singletonOfNotTail_ne i j hi hj hij) b a).symm
      · by_cases hl : l = 2
        · subst l
          have hki : k = i := by omega
          subst k
          simp [blockRootSubgroup, singletonOfNotTail, smallRootSubgroup,
            hi, hj] at hx hy
          obtain ⟨a, rfl⟩ := hx
          obtain ⟨b, rfl⟩ := hy
          exact smallRoot_rowToTail_commute F _ _
            (singletonOfNotTail_ne i j hi hj hij) a b
        · have hki : k = i := by omega
          have hlj : l = j := by omega
          subst k
          subst l
          simp [blockRootSubgroup, singletonOfNotTail, smallRootSubgroup,
            hi, hj] at hx hy
          obtain ⟨a, rfl⟩ := hx
          obtain ⟨b, rfl⟩ := hy
          rw [commute_iff_eq, x_mul, x_mul]
          congr 1
          exact add_comm _ _

theorem blockRoot_commutator_mem (F : CompleteMatrixFamily R κ) :
    ∀ (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
      ∀ x ∈ blockRootSubgroup F i j hij,
        ∀ y ∈ blockRootSubgroup F j k hjk,
          ⁅x, y⁆ ∈ blockRootSubgroup F i k hik := by
  intro i j k hij hjk hik x hx y hy
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try omega
  all_goals
    simp_all [blockRootSubgroup, singletonOfNotTail, smallRootSubgroup]
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    first
    | exact ⟨a * b,
        (smallRoot_rowToTail_commutator F _ _ (by decide) a b).symm⟩
    | exact ⟨a * b,
        (tailToRow_smallRoot_commutator F _ _ (by decide) a b).symm⟩
    | exact ⟨a * b,
        (rowToTail_tailToRow_commutator F _ _ (by decide) a b).symm⟩

theorem blockRoot_commutator_surjective (F : CompleteMatrixFamily R κ) :
    ∀ (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
      ∀ z ∈ blockRootSubgroup F i k hik,
        ∃ x ∈ blockRootSubgroup F i j hij,
          ∃ y ∈ blockRootSubgroup F j k hjk, ⁅x, y⁆ = z := by
  intro i j k hij hjk hik z hz
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try omega
  all_goals
    simp_all [blockRootSubgroup, singletonOfNotTail, smallRootSubgroup]
    obtain ⟨c, rfl⟩ := hz
    first
    | refine ⟨smallRoot (κ := κ) _ _ (by decide) c, ⟨c, rfl⟩,
        rowToTail F _ 1, ⟨1, rfl⟩, ?_⟩
      simpa using smallRoot_rowToTail_commutator F _ _ (by decide) c 1
    | refine ⟨tailToRow F _ c, ⟨c, rfl⟩,
        smallRoot (κ := κ) _ _ (by decide) 1, ⟨1, rfl⟩, ?_⟩
      simpa using tailToRow_smallRoot_commutator F _ _ (by decide) c 1
    | refine ⟨rowToTail F _ c, ⟨c, rfl⟩,
        tailToRow F _ 1, ⟨1, rfl⟩, ?_⟩
      simpa [smallRoot] using
        rowToTail_tailToRow_commutator F _ _ (by decide) c 1

/-- The strongly graded three-block `A₂` system inside the higher-rank
Steinberg group. -/
def blockA2System (F : CompleteMatrixFamily R κ) :
    A2System (SteinbergGroup (Fin 2 ⊕ κ) R) where
  root := blockRootSubgroup F
  generate := blockRootSet_generate F
  commute := blockRoot_commute F
  commutator_mem := blockRoot_commutator_mem F
  commutator_surjective := blockRoot_commutator_surjective F

end SteinbergBlockRoot
end GroupApproximation
