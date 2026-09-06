import GroupApproximation.CharClass.LIXVLineBundles
import GroupApproximation.CharClass.SplitRelationRange

/-!
# The split relation for `V = 𝟏³ ⊕ H`

The splitting principle wants the summands as a family indexed by a natural.
`cc-lix-odd`'s lines are indexed by `Fin 3 ⊕ HBlk dd`, so the flat family reads
the index modulo the rank rather than being cut off with a zero bundle: there is
no zero `Bundle` to cut off with, and wrapping agrees with the intended family on
the whole range, which is all the split relation ever looks at.

Wrapping has a second benefit worth stating.  Every line in the flat family is a
genuine line, so its trace is one at *every* index, not only below the rank.  The
restricted hypothesis `cc-wu` asked for is therefore not needed here, but the
restricted form is used anyway, because taking the roots as a parameter keeps the
conclusion free of a dependent proof argument.

## Main declarations

* `vLineFlatBundle` — the lines of `V`, indexed by a natural.
* `sum_vLineFlatBundle` — the decomposition over `Finset.range (lixRank dd)`.
* `splitRelation_V` — **the split relation for `V`.**
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.CharClass.LH
open GroupApproximation.CharClass.LHCast

noncomputable section

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

theorem lixRank_pos (dd : Fin ℓ → ℕ) : 0 < lixRank dd := by
  rw [lixRank]
  omega

/-- The lines of `V`, indexed by a natural, reading the index modulo the rank. -/
def vLineFlatBundle (dd : Fin ℓ → ℕ) (l : ℕ) : Bundle (baseY dd) (VIdx dd) :=
  vLineYBundle ((vIndexEquiv dd).symm ⟨l % lixRank dd, Nat.mod_lt _ (lixRank_pos dd)⟩)

/-- Every line of the flat family has trace one, at every index. -/
theorem trace_vLineFlatBundle (dd : Fin ℓ → ℕ) (l : ℕ) (y : baseY dd) :
    Matrix.trace ((vLineFlatBundle dd l) y) = 1 :=
  trace_vLineY _ y

/-- On the range the flat family is the intended one. -/
theorem vLineFlatBundle_apply_lt (dd : Fin ℓ → ℕ) (l : ℕ) (hl : l < lixRank dd)
    (y : baseY dd) : (vLineFlatBundle dd l) y = vLineYFlat dd y l := by
  have h : (⟨l % lixRank dd, Nat.mod_lt _ (lixRank_pos dd)⟩ : Fin (lixRank dd))
      = ⟨l, hl⟩ := Fin.ext (Nat.mod_eq_of_lt hl)
  show vLineY ((vIndexEquiv dd).symm ⟨l % lixRank dd, _⟩) y = _
  rw [h, vLineYFlat, dif_pos hl]

/-- **The decomposition of `V` into the flat family.** -/
theorem sum_vLineFlatBundle (dd : Fin ℓ → ℕ) (y : baseY dd) :
    (vBundleY dd) y = ∑ l ∈ Finset.range (lixRank dd), (vLineFlatBundle dd l) y := by
  show VmatY y = _
  rw [VmatY_eq_sum_rangeY y]
  exact Finset.sum_congr rfl fun l hl =>
    (vLineFlatBundle_apply_lt dd l (Finset.mem_range.mp hl) y).symm

theorem rank_vBundleY_lixRank (dd : Fin ℓ → ℕ) (y : baseY dd) :
    (vBundleY dd).rank y = lixRank dd := rank_vBundleY dd y

theorem trace_vLineFlatBundle_lt (dd : Fin ℓ → ℕ) (l : ℕ) (_hl : l < lixRank dd)
    (y : baseY dd) : Matrix.trace ((vLineFlatBundle dd l) y) = 1 :=
  trace_vLineFlatBundle dd l y

/-- **The split relation for `V`.**  The roots are a parameter, agreeing with the
Euler classes of the lines on the range. -/
theorem splitRelation_V (dd : Fin ℓ → ℕ) [CompactSpace (baseY dd)] [Nonempty (baseY dd)]
    (root : ℕ → Hmod2 (TopCat.of (baseY dd)) 2)
    (hroot : ∀ l, ∀ hl : l < lixRank dd,
      root l = lineEulerOf (vLineFlatBundle dd l) (trace_vLineFlatBundle_lt dd l hl)) :
    LerayHirschData.SplitRelation
      (lerayHirschData_of_graded
        (lerayHirschGraded_compact (vBundleY dd) (lixRank dd)
          (rank_vBundleY_lixRank dd) (lixRank_pos dd)))
      (lixRank dd) root :=
  splitRelation_of_sum_lt (vBundleY dd) (lixRank dd) (lixRank_pos dd)
    (rank_vBundleY_lixRank dd) (vLineFlatBundle dd) (trace_vLineFlatBundle_lt dd)
    (sum_vLineFlatBundle dd) root hroot

end

end GroupApproximation.CharClass
