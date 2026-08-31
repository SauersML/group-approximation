import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Finite products in a normal closure

This file isolates the purely group-theoretic content of a relator diagram:
an element of a normal closure is represented by a finite product of conjugates
of defining relators and their inverses.  The natural-number index records an
upper bound for the number of relator occurrences.
-/

namespace GroupApproximation
namespace RelatorDefectBudget

variable {G : Type*} [Group G]

/-- `IsRelatorProduct R n w` records that `w` is a product of at most `n`
conjugates of elements of `R` and of their inverses. -/
inductive IsRelatorProduct (R : Set G) : ℕ → G → Prop
  | one : IsRelatorProduct R 0 1
  | base {r : G} (hr : r ∈ R) : IsRelatorProduct R 1 r
  | inv {n : ℕ} {w : G} (h : IsRelatorProduct R n w) : IsRelatorProduct R n w⁻¹
  | conj {n : ℕ} {w : G} (c : G) (h : IsRelatorProduct R n w) :
      IsRelatorProduct R n (c * w * c⁻¹)
  | mul {m n : ℕ} {a b : G} (ha : IsRelatorProduct R m a)
      (hb : IsRelatorProduct R n b) : IsRelatorProduct R (m + n) (a * b)

/-- The elements carrying some finite relator-product bound. -/
def budgetSubgroup (R : Set G) : Subgroup G where
  carrier := {w : G | ∃ n : ℕ, IsRelatorProduct R n w}
  one_mem' := ⟨0, IsRelatorProduct.one⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨m + n, hm.mul hn⟩
  inv_mem' := by
    intro a ha
    obtain ⟨n, hn⟩ := ha
    exact ⟨n, hn.inv⟩

instance budgetSubgroup_normal (R : Set G) : (budgetSubgroup R).Normal where
  conj_mem := by
    intro a ha c
    obtain ⟨n, hn⟩ := ha
    exact ⟨n, hn.conj c⟩

/-- Every element of the normal closure of `R` has a finite relator-product
certificate. -/
theorem exists_isRelatorProduct {R : Set G} {w : G}
    (hw : w ∈ Subgroup.normalClosure R) : ∃ n : ℕ, IsRelatorProduct R n w := by
  have hsub : R ⊆ (budgetSubgroup R : Set G) := by
    intro r hr
    exact ⟨1, IsRelatorProduct.base hr⟩
  exact Subgroup.normalClosure_le_normal hsub hw

/-- A relator-product certificate of index zero can only represent the
identity. -/
theorem IsRelatorProduct.eq_one_of_index_zero {R : Set G} {w : G}
    (h : IsRelatorProduct R 0 w) : w = 1 := by
  have hzero : ∀ {n : ℕ} {g : G}, IsRelatorProduct R n g → n = 0 → g = 1 := by
    intro n g hg
    induction hg with
    | one => intro _; rfl
    | base _ => intro hindex; omega
    | inv h ih =>
        intro hindex
        rw [ih hindex, inv_one]
    | conj c h ih =>
        intro hindex
        rw [ih hindex]
        simp
    | @mul m n a b ha hb iha ihb =>
        intro hindex
        have hm : m = 0 := by omega
        have hn : n = 0 := by omega
        rw [iha hm, ihb hn, mul_one]
  exact hzero h rfl

end RelatorDefectBudget
end GroupApproximation
