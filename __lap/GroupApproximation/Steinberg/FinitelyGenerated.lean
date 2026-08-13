import GroupApproximation.Steinberg.Perfect
import GroupApproximation.Leavitt.ElementaryGroup

/-!
# Finite generation of characteristic-two Steinberg groups

For a finite-type algebra over `𝔽₂`, finitely many coefficient generators in
all root positions generate the Steinberg group.  Addition uses the root
group law and multiplication uses a commutator through a third index.
-/

namespace GroupApproximation
namespace SteinbergGroup

open scoped commutatorElement

variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]

noncomputable def finiteGenerators [DecidableEq R] (n : ℕ)
    (s : Finset R) : Finset (SteinbergGroup (Fin n) R) := by
  classical
  exact Finset.univ.biUnion fun i : Fin n ↦
    Finset.univ.biUnion fun j : Fin n ↦
      if h : i ≠ j then (insert 1 s).image (x i j h) else ∅

omit [Algebra (ZMod 2) R] in
theorem mem_finiteGenerators [DecidableEq R] (n : ℕ) (s : Finset R)
    (z : SteinbergGroup (Fin n) R) :
    z ∈ finiteGenerators n s ↔
      ∃ (i j : Fin n) (h : i ≠ j) (a : R),
        a ∈ insert 1 s ∧ x i j h a = z := by
  classical
  constructor
  · intro hz
    unfold finiteGenerators at hz
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hi
    by_cases h : i ≠ j
    · rw [dif_pos h] at hj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨i, j, h, a, ha, rfl⟩
    · rw [dif_neg h] at hj
      simp at hj
  · rintro ⟨i, j, h, a, ha, rfl⟩
    unfold finiteGenerators
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ j, ?_⟩
    rw [dif_pos h]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

/-- Coefficients whose root elements in every position lie in `H` form an
`𝔽₂`-subalgebra. -/
def coefficientSubalgebra (n : ℕ) (hn : 2 < n)
    (H : Subgroup (SteinbergGroup (Fin n) R))
    (hunit : ∀ (i j : Fin n) (h : i ≠ j), x i j h (1 : R) ∈ H) :
    Subalgebra (ZMod 2) R where
  carrier := {a | ∀ (i j : Fin n) (h : i ≠ j), x i j h a ∈ H}
  add_mem' := by
    intro a b ha hb i j hij
    rw [← x_mul]
    exact H.mul_mem (ha i j hij) (hb i j hij)
  mul_mem' := by
    intro a b ha hb i j hij
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
    have hik : i ≠ k := hki.symm
    have hc : ⁅x i k hik a, x k j hkj b⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem
        (H.mul_mem (H.mul_mem (ha i k hik) (hb k j hkj))
          (H.inv_mem (ha i k hik)))
        (H.inv_mem (hb k j hkj))
    rw [x_commutator i k j hik hkj hij] at hc
    exact hc
  algebraMap_mem' := by
    intro z
    have hz : z = 0 ∨ z = 1 := by
      fin_cases z
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hz with rfl | rfl
    · intro i j hij
      simpa only [map_zero, x_zero] using H.one_mem
    · intro i j hij
      simpa only [map_one] using hunit i j hij

/-- `St_n(R)` is finitely generated when `R` is a finite-type
`𝔽₂`-algebra and `n ≥ 3`. -/
theorem finitelyGenerated [Algebra.FiniteType (ZMod 2) R]
    (n : ℕ) (hn : 2 < n) : Group.FG (SteinbergGroup (Fin n) R) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ZMod 2) (A := R)
  let t := finiteGenerators n s
  let H : Subgroup (SteinbergGroup (Fin n) R) :=
    Subgroup.closure (t : Set (SteinbergGroup (Fin n) R))
  have hunit : ∀ (i j : Fin n) (h : i ≠ j), x i j h (1 : R) ∈ H := by
    intro i j hij
    apply Subgroup.subset_closure
    exact (mem_finiteGenerators n s _).mpr
      ⟨i, j, hij, 1, Finset.mem_insert_self 1 s, rfl⟩
  let C : Subalgebra (ZMod 2) R := coefficientSubalgebra n hn H hunit
  have hgen : (s : Set R) ⊆ (C : Set R) := by
    intro a ha i j hij
    apply Subgroup.subset_closure
    exact (mem_finiteGenerators n s _).mpr
      ⟨i, j, hij, a, Finset.mem_insert_of_mem ha, rfl⟩
  have hC : C = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Algebra.adjoin_le hgen
  have hH : H = ⊤ := by
    apply top_unique
    intro g _
    apply PresentedGroup.generated_by (relations (I := Fin n) (R := R)) H ?_ g
    rintro ⟨i, j, hij, a⟩
    change x i j hij a ∈ H
    have ha : a ∈ C := by simp [hC]
    exact ha i j hij
  exact (Group.fg_iff').mpr ⟨t.card, t, rfl, hH⟩

end SteinbergGroup
end GroupApproximation
