import GroupApproximation.CharClass.LerayHirschFinite
import GroupApproximation.CharClass.ProjectiveSpaceCharts

/-!
# Recognising a cover as a fold, and the chart cover of `ℂP^d`

`bijective_lhSum_of_finite_cover` asks for its cover as a list folded by `⊔`,
because that is the shape the induction on the length consumes.  This file says
when such a fold is everything, and applies it to the standard charts.

## Main declarations

* `mem_foldr_sup`, `foldr_sup_eq_top` — a fold of `⊔` is everything exactly when
  every point lies in one of the pieces.
* `chartOpen_cover` — **the standard charts of `ℂP^d`, as a fold**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace

noncomputable section

variable {X : TopCat.{0}}

theorem mem_foldr_sup (L : List (Opens X)) (A : Opens X) (x : X) :
    x ∈ L.foldr (· ⊔ ·) A ↔ (x ∈ A ∨ ∃ B ∈ L, x ∈ B) := by
  induction L with
  | nil => simp
  | cons C L' ih =>
    have hsup : x ∈ (C ⊔ L'.foldr (· ⊔ ·) A) ↔ (x ∈ C ∨ x ∈ L'.foldr (· ⊔ ·) A) := by
      constructor
      · intro hx
        have hx' : x ∈ ((C : Set X) ∪ ((L'.foldr (· ⊔ ·) A : Opens X) : Set X)) := by
          rw [← Opens.coe_sup]
          exact hx
        exact hx'
      · intro hx
        show x ∈ ((C ⊔ L'.foldr (· ⊔ ·) A : Opens X) : Set X)
        rw [Opens.coe_sup]
        exact hx
    show x ∈ (C ⊔ L'.foldr (· ⊔ ·) A) ↔ _
    rw [hsup, ih]
    constructor
    · rintro (h1 | h2 | ⟨B, hB, hxB⟩)
      · exact Or.inr ⟨C, by simp, h1⟩
      · exact Or.inl h2
      · exact Or.inr ⟨B, by simp [hB], hxB⟩
    · rintro (h1 | ⟨B, hB, hxB⟩)
      · exact Or.inr (Or.inl h1)
      · rcases List.mem_cons.mp hB with rfl | hB'
        · exact Or.inl hxB
        · exact Or.inr (Or.inr ⟨B, hB', hxB⟩)

/-- **A fold of `⊔` is everything** exactly when every point lies in one of the pieces. -/
theorem foldr_sup_eq_top (L : List (Opens X)) (A : Opens X)
    (h : ∀ x : X, x ∈ A ∨ ∃ B ∈ L, x ∈ B) : L.foldr (· ⊔ ·) A = ⊤ :=
  Opens.ext (Set.eq_univ_of_forall fun x => (mem_foldr_sup L A x).mpr (h x))

end

end LH

namespace CPn

open TopologicalSpace
open GroupApproximation.CharClass.LH

noncomputable section

/-- **The standard charts of `ℂP^d` cover**, in the fold shape the Leray–Hirsch
induction takes.  The zeroth chart is the base of the fold and the rest are the
list. -/
theorem chartOpen_cover (d : ℕ) :
    (List.ofFn (fun i : Fin d => chartOpenAt (d := d) i.succ)).foldr (· ⊔ ·)
      (chartOpenAt (d := d) 0) = ⊤ := by
  refine foldr_sup_eq_top _ _ fun z => ?_
  obtain ⟨i, hi⟩ := exists_mem_chartOpenAt z
  revert hi
  induction i using Fin.cases with
  | zero => exact fun hi => Or.inl hi
  | succ j =>
    exact fun hi => Or.inr ⟨chartOpenAt j.succ, by simp, hi⟩

end

end CPn
end CharClass
end GroupApproximation
