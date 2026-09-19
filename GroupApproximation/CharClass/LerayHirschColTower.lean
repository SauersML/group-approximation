import GroupApproximation.CharClass.LerayHirschFreeExists

/-!
# A column, read as a tower

The uniqueness half runs the reconciliation backwards: `peelFreeAt` speaks about
towers, and what the ladder has is a column.  So a column of length the rank has to
be presented as a tower of length the degree, which is this file.

The two conditions in the definition are the two the reconciliation always needs.
A tower index beyond the column's length has no coefficient to read, and a tower
index past `k` would ask the column for a negative degree; both give zero, which is
what the tower's own vanishing above the rank makes harmless.

## Main declarations

* `colTower` — a column, read as a tower.
* `towerCoeff_colTower` — reading it back gives the column.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-- **A column, read as a tower.**  The tower's `j`-th coefficient is the column's
at index `k - j`, when there is one. -/
def colTower (m k : ℕ) (a : (i : Fin (d + 2)) → Hmod2 (TopCat.of U) (m + 2 * k - 2 * (i : ℕ))) :
    (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j) :=
  fun j => if h : j ≤ k ∧ k - j < d + 2 then
      cohCast (show m + 2 * k - 2 * ((⟨k - j, h.2⟩ : Fin (d + 2)) : ℕ) = m + 2 * j by
        have := h.1
        show m + 2 * k - 2 * (k - j) = m + 2 * j
        omega) (a ⟨k - j, h.2⟩)
    else 0

theorem colTower_of (m k : ℕ)
    (a : (i : Fin (d + 2)) → Hmod2 (TopCat.of U) (m + 2 * k - 2 * (i : ℕ)))
    {j : ℕ} (h : j ≤ k ∧ k - j < d + 2) :
    colTower U d m k a j
      = cohCast (show m + 2 * k - 2 * ((⟨k - j, h.2⟩ : Fin (d + 2)) : ℕ) = m + 2 * j by
          have := h.1
          show m + 2 * k - 2 * (k - j) = m + 2 * j
          omega) (a ⟨k - j, h.2⟩) := dif_pos h

theorem colTower_of_not (m k : ℕ)
    (a : (i : Fin (d + 2)) → Hmod2 (TopCat.of U) (m + 2 * k - 2 * (i : ℕ)))
    {j : ℕ} (h : ¬ (j ≤ k ∧ k - j < d + 2)) : colTower U d m k a j = 0 := dif_neg h

end

end LH
end CharClass
end GroupApproximation
