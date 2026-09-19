import GroupApproximation.Analysis.TwoSidedRegularCommutant
import Mathlib.GroupTheory.Perm.Basic

/-!
# The symmetric group of `ℕ` has infinite conjugacy classes

Fourth module of the `LI.06d` lane (`p:limits-trace`).  The lane's witness
group must be ICC — every nonidentity conjugacy class infinite — so that the
two-sided commutant computation applies and `L(G)` is an infinite-dimensional
factor.  The full symmetric group of `ℕ` is the classical elementary example:
a nonidentity permutation moves some point `a`, and conjugating by the
transpositions `(σa, n)` produces, for every `n` outside `{a, σa}`, a
conjugate sending `a` to `n` — infinitely many distinct conjugates.
-/

namespace GroupApproximation
namespace PermutationICC

open TwoSidedRegularCommutant

/-- **`Perm ℕ` is ICC.**  Every nonidentity conjugacy class is infinite. -/
theorem isICC_perm : IsICC (Equiv.Perm ℕ) := by
  intro σ hσ
  obtain ⟨a, ha⟩ : ∃ a : ℕ, σ a ≠ a := by
    by_contra hall
    exact hσ (Equiv.ext fun a ↦ by
      by_contra hne
      exact hall ⟨a, hne⟩)
  -- evaluating the conjugates at `a` reaches every point outside `{a, σa}`
  have hsub : (Set.univ \ {a, σ a} : Set ℕ)
      ⊆ (fun π : Equiv.Perm ℕ ↦ π a) '' {x | IsConj σ x} := by
    rintro n ⟨-, hn⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hn
    obtain ⟨hna, hnσa⟩ := hn
    refine ⟨Equiv.swap (σ a) n * σ * (Equiv.swap (σ a) n)⁻¹, ?_, ?_⟩
    · exact isConj_iff.mpr ⟨Equiv.swap (σ a) n, rfl⟩
    · show (Equiv.swap (σ a) n * σ * (Equiv.swap (σ a) n)⁻¹) a = n
      rw [Equiv.swap_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hna)]
      exact Equiv.swap_apply_left (σ a) n
  have hbase : (Set.univ \ {a, σ a} : Set ℕ).Infinite :=
    Set.infinite_univ.sdiff ((Set.finite_singleton (σ a)).insert a)
  have himg : ((fun π : Equiv.Perm ℕ ↦ π a) '' {x | IsConj σ x}).Infinite :=
    hbase.mono hsub
  exact himg.of_image

/-- `Perm ℕ` is infinite — the conjugacy class of one transposition already
is. -/
theorem infinite_perm : Infinite (Equiv.Perm ℕ) := by
  have hne : Equiv.swap (0 : ℕ) 1 ≠ 1 := by
    intro h
    have h0 := congrArg (fun π : Equiv.Perm ℕ ↦ π 0) h
    simp only [Equiv.swap_apply_left, Equiv.Perm.one_apply] at h0
    exact one_ne_zero h0
  exact Set.infinite_univ_iff.mp
    ((isICC_perm _ hne).mono (Set.subset_univ _))

end PermutationICC
end GroupApproximation
