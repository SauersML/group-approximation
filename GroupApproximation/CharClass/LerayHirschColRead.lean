import GroupApproximation.CharClass.LerayHirschColTower

/-!
# Reading a column back out of its tower

`colTower` presents a column as a tower; the uniqueness half then needs that
reading the tower's coefficients back at the column's index returns the column.
Both directions of the reflection are dependent rewrites — the coefficient's type
moves with its index, and on this side the index is a `Fin` — so each gets a
transport lemma rather than a `rw`.

## Main declarations

* `col_index_congr` — transporting a column coefficient along an equality of index.
* `towerCoeff_colTower` — **reading the tower back gives the column**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-- Transporting a column coefficient along an equality of its index. -/
theorem col_index_congr (m k : ℕ)
    (a : (i : Fin (d + 2)) → Hmod2 (TopCat.of U) (m + 2 * k - 2 * (i : ℕ)))
    {i j : Fin (d + 2)} (h : i = j) {D : ℕ}
    (hD₁ : m + 2 * k - 2 * (i : ℕ) = D) (hD₂ : m + 2 * k - 2 * (j : ℕ) = D) :
    cohCast hD₁ (a i) = cohCast hD₂ (a j) := by
  subst h
  rfl

/-- **Reading the tower back gives the column.** -/
theorem towerCoeff_colTower (m k : ℕ)
    (a : (i : Fin (d + 2)) → Hmod2 (TopCat.of U) (m + 2 * k - 2 * (i : ℕ)))
    {i : ℕ} (hik : i ≤ k) (hid : i < d + 2) :
    towerCoeff U m k (colTower U d m k a) i = a ⟨i, hid⟩ := by
  have hj : k - i ≤ k := by omega
  have hjd : k - (k - i) < d + 2 := by omega
  rw [towerCoeff_of_le U m k _ hik, colTower_of U d m k a ⟨hj, hjd⟩]
  have hfin : (⟨k - (k - i), hjd⟩ : Fin (d + 2)) = ⟨i, hid⟩ := by
    apply Fin.ext
    show k - (k - i) = i
    omega
  rw [cohCast_cohCast]
  exact (col_index_congr U d m k a hfin _ rfl).trans (cohCast_rfl _)

end

end LH
end CharClass
end GroupApproximation
