import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.PropertyT.FinitelyGeneratedRing

/-!
# `EL_n(R)` is finitely generated over a finitely generated ring

`non_mf_groups_exist.tex`, proof of `thm:full-defect-ring`:

> The ring `𝒞` is finitely generated, so both groups have property~(T)
> by [EJZ], and `B` is finitely generated [BHV, Theorem 1.3.1].

`Leavitt.ElementaryGroup` proves this for a finitely generated `𝔽₂`-algebra
(`elementaryGroup_finitelyGenerated`) and for a finitely generated algebra over
a finite field (`elementaryGroup_finitelyGenerated_finiteField`).  Neither
applies to `𝒞`, which is a `ℤ`-algebra of characteristic zero.  This module
gives the version for `IsFinitelyGeneratedRing`, which is the printed
hypothesis and covers both existing cases.

## What changes in the proof

Only the coefficient object.  The existing proof collects the coefficients
whose elementary roots lie in a subgroup `H` into a *subalgebra*; over `ℤ`
there is no algebra structure to use, so the same set is collected into a
**subring**.  It is a subring for exactly the reasons it was a subalgebra:
closed under addition because `e_ij(a)e_ij(b) = e_ij(a+b)`, under negation
because `e_ij(-a)` is the inverse, and under multiplication by the Steinberg
commutator through a third index — which is where `n ≥ 3` is used.  The unit
`1` is in it by construction, and that is all a subring needs, so no
`algebraMap` clause is required at all.

`finiteElementaryGenerators` of `ElementaryGroup` is not reused: its section
carries an `[Algebra (ZMod 2) R]` instance that the definition does not use but
does record, so it cannot be applied here.  `rootGenerators` below is the same
finite set without that instance.
-/

namespace GroupApproximation

open scoped commutatorElement

variable {R : Type*} [Ring R]

/-- The finite generating set: the elementary roots at the ring generators and
at `1`.  This is `finiteElementaryGenerators` without the unused
`Algebra (ZMod 2)` instance of its section. -/
noncomputable def rootGenerators [DecidableEq R] (n : ℕ) (s : Finset R) :
    Finset (Matrix (Fin n) (Fin n) R)ˣ :=
  Finset.univ.biUnion fun i : Fin n ↦
    Finset.univ.biUnion fun j : Fin n ↦
      if h : i ≠ j then (insert 1 s).image (elementaryUnit i j h) else ∅

theorem mem_rootGenerators [DecidableEq R] (n : ℕ) (s : Finset R)
    (z : (Matrix (Fin n) (Fin n) R)ˣ) :
    z ∈ rootGenerators n s ↔
      ∃ (i j : Fin n) (h : i ≠ j) (a : R),
        a ∈ insert 1 s ∧ elementaryUnit i j h a = z := by
  constructor
  · intro hz
    unfold rootGenerators at hz
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hi
    by_cases h : i ≠ j
    · rw [dif_pos h] at hj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨i, j, h, a, ha, rfl⟩
    · rw [dif_neg h] at hj
      simp at hj
  · rintro ⟨i, j, h, a, ha, rfl⟩
    unfold rootGenerators
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, ?_⟩
    rw [dif_pos h]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

/-- The coefficients whose elementary roots all lie in `H` form a subring, as
soon as the root at `1` does and there are at least three indices. -/
def elementaryCoefficientSubring (n : ℕ) (hn : 2 < n)
    (H : Subgroup (Matrix (Fin n) (Fin n) R)ˣ)
    (hunit : ∀ (i j : Fin n) (h : i ≠ j), elementaryUnit i j h (1 : R) ∈ H) :
    Subring R where
  carrier := {a | ∀ (i j : Fin n) (h : i ≠ j), elementaryUnit i j h a ∈ H}
  zero_mem' := by
    intro i j hij
    simpa only [elementaryUnit_zero] using H.one_mem
  one_mem' := hunit
  add_mem' := by
    intro a b ha hb i j hij
    rw [← elementaryUnit_mul]
    exact H.mul_mem (ha i j hij) (hb i j hij)
  neg_mem' := by
    intro a ha i j hij
    have hmul : elementaryUnit i j hij (-a) * elementaryUnit i j hij a = 1 := by
      rw [elementaryUnit_mul, neg_add_cancel, elementaryUnit_zero]
    have hinv : elementaryUnit i j hij (-a) = (elementaryUnit i j hij a)⁻¹ :=
      eq_inv_of_mul_eq_one_left hmul
    rw [hinv]
    exact H.inv_mem (ha i j hij)
  mul_mem' := by
    intro a b ha hb i j hij
    obtain ⟨l, hli, hlj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
    have hil : i ≠ l := hli.symm
    have hc : ⁅elementaryUnit i l hil a, elementaryUnit l j hlj b⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem
        (H.mul_mem (H.mul_mem (ha i l hil) (hb l j hlj))
          (H.inv_mem (ha i l hil)))
        (H.inv_mem (hb l j hlj))
    rw [elementaryUnit_commutator i l j hil hlj hij a b] at hc
    exact hc

/-- **`EL_n(R)` is finitely generated whenever `R` is a finitely generated
ring and `n ≥ 3`.**  This is the printed `B` clause at a general coefficient
ring; the printed hypothesis is exactly `IsFinitelyGeneratedRing`. -/
theorem elementaryGroup_finitelyGenerated_of_isFinitelyGeneratedRing
    (hR : IsFinitelyGeneratedRing R) (n : ℕ) (hn : 2 < n) :
    Group.FG (elementaryGroup (Fin n) R) := by
  classical
  obtain ⟨s, hs⟩ := hR
  set t : Finset (Matrix (Fin n) (Fin n) R)ˣ := rootGenerators n s with ht
  set H : Subgroup (Matrix (Fin n) (Fin n) R)ˣ :=
    Subgroup.closure (t : Set (Matrix (Fin n) (Fin n) R)ˣ) with hH
  have hunit : ∀ (i j : Fin n) (h : i ≠ j),
      elementaryUnit i j h (1 : R) ∈ H := by
    intro i j hij
    apply Subgroup.subset_closure
    exact (mem_rootGenerators n s _).mpr
      ⟨i, j, hij, 1, Finset.mem_insert_self 1 s, rfl⟩
  set C : Subring R := elementaryCoefficientSubring n hn H hunit with hCdef
  have hgen : (s : Set R) ⊆ (C : Set R) := by
    intro a ha i j hij
    apply Subgroup.subset_closure
    exact (mem_rootGenerators n s _).mpr
      ⟨i, j, hij, a, Finset.mem_insert_of_mem ha, rfl⟩
  have hC : C = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Subring.closure_le.mpr hgen
  have heq : H = elementaryGroup (Fin n) R := by
    apply le_antisymm
    · rw [hH, Subgroup.closure_le]
      intro z hz
      obtain ⟨i, j, hij, a, -, rfl⟩ := (mem_rootGenerators n s z).mp hz
      exact elementaryUnit_mem i j hij a
    · rw [elementaryGroup, Subgroup.closure_le]
      rintro _ ⟨i, j, hij, a, rfl⟩
      have ha : a ∈ C := by simp [hC]
      exact ha i j hij
  exact (Group.fg_iff_subgroup_fg (elementaryGroup (Fin n) R)).mpr ⟨t, heq⟩

end GroupApproximation
