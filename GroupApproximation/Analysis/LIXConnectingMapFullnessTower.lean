import GroupApproximation.Analysis.LIXConnectingMapFullnessSum
import GroupApproximation.Analysis.LIXLimitTower

set_option autoImplicit false

/-!
# Stagewise fullness of the LIX tower

The manuscript's §5 in the form the simplicity bridge consumes: for every stage `k` and
every nonzero `a ∈ A_k` there is a later stage `j` at which the composite connecting map
carries `a` to a full element.

The statement is over an arbitrary `LIX.CStarTower` whose successor maps are the `STW59.connect`
of `Analysis/LIXConnectingMap.lean`, rather than over a particular tower, so that this file
does not have to import the concrete `lixTower`; `Analysis/LIXLimitAlgebra.lean`'s
`lixTower_succHom` discharges the hypothesis by `rfl` and
`CStarTower.isSimpleCStar_limit_of_ne_zero` then applies directly.

## The argument

1. `a ≠ 0` means some fibre value `a(w₀)` is nonzero (`STW59.stageAlgebra_eq_zero_iff`), and the
   set of such `w` is open because the fibre value depends continuously on the point.
2. `STW59.exists_stagePoint_mem_of_isOpen` produces `i ≥ k` whose stage point `x_i` projects
   into that open set.
3. The pulled-back block of `connect` carries nonvanishing up the tower
   (`STW59.stageEval_climb_ne_zero`), so `φ_{k,i}(a)` is nonzero at `x_i`.
4. One more step is full: `STW59.isFull_connect_of_stageEval_ne_zero`.

**No positivity is used.**  The witness is `j = i + 1`, one step past the stage where the
point evaluation catches the nonvanishing, exactly as in the manuscript.
-/

namespace GroupApproximation
namespace STW59

open scoped Matrix ComplexOrder CStarAlgebra

noncomputable section

namespace Gen

variable (n : ℕ)

/-- The fibre value of a section depends continuously on the point. -/
theorem continuous_stageEval (k : ℕ) (a : StageAlgebra n k) :
    Continuous fun w : baseX n k => stageEval n k w a := by
  refine continuous_matrix fun s t => ?_
  exact ((toFunctionMatrix (a : SectionAlgebra (baseX n k) (EIdx n k))) s t).continuous

/-- The set of points at which a section does not vanish is open. -/
theorem isOpen_stageEval_ne_zero (k : ℕ) (a : StageAlgebra n k) :
    IsOpen ((fun w : baseX n k => stageEval n k w a) ⁻¹'
      {(0 : Matrix (EIdx n k) (EIdx n k) ℂ)}ᶜ) :=
  IsOpen.preimage (continuous_stageEval n k a) isOpen_compl_singleton

/-- **Nonvanishing travels up the tower.**  The `(1,1)` block of `φ_i` is `π_i^*`, so if `a`
does not vanish at `π_{k,i}(w)` then `φ_{k,i}(a)` does not vanish at `w`.

Both `basePr n h w = w` for `h : k ≤ k` and `basePr n h' (baseProj n i w) = basePr n h w` are
`rfl`, because `Fin.castLE` of a proof of `k ≤ k` is the identity up to structure eta; that is
why no transport appears anywhere below. -/
theorem stageEval_climb_ne_zero {T : LIX.CStarTower (StageAlgebra n)}
    (hT : ∀ i, T.succHom i = connect n i) {k : ℕ} {a : StageAlgebra n k} :
    ∀ (i : ℕ) (h : k ≤ i) (w : baseX n i),
      stageEval n k (basePr n h w) a ≠ 0 → stageEval n i w (T.climb i k a) ≠ 0 := by
  intro i
  induction i with
  | zero =>
      intro h w ha
      obtain rfl : k = 0 := Nat.le_zero.mp h
      rw [T.climb_self]
      exact ha
  | succ i ih =>
      intro h w ha
      rcases Nat.lt_or_ge k (i + 1) with hlt | hge
      · have hki : k ≤ i := Nat.lt_succ_iff.mp hlt
        rw [T.climb_succ hki, hT i]
        refine stageEval_connect_ne_zero_of_pull n i w ?_
        exact ih hki (baseProj n i w) ha
      · obtain rfl : k = i + 1 := le_antisymm h hge
        rw [T.climb_self]
        exact ha

/-- **Stagewise fullness.**  For every nonzero `a ∈ A_k` there is `j ≥ k` with `φ_{k,j}(a)`
full in `A_j`. -/
theorem isFull_climb_of_ne_zero {T : LIX.CStarTower (StageAlgebra n)}
    (hT : ∀ i, T.succHom i = connect n i) (k : ℕ) (a : StageAlgebra n k) (hne : a ≠ 0) :
    ∃ j, k ≤ j ∧ GroupApproximation.LIX.IsFull (T.climb j k a) := by
  obtain ⟨w₀, hw₀⟩ : ∃ w : baseX n k, stageEval n k w a ≠ 0 := by
    by_contra hcon
    refine hne (stageAlgebra_eq_zero_iff.mpr fun w => ?_)
    by_contra hw
    exact hcon ⟨w, hw⟩
  obtain ⟨i, h, hmem⟩ := exists_stagePoint_mem_of_isOpen n (isOpen_stageEval_ne_zero n k a)
    ⟨w₀, hw₀⟩
  refine ⟨i + 1, h.trans (Nat.le_succ i), ?_⟩
  have hb : stageEval n i (stagePoint n i) (T.climb i k a) ≠ 0 :=
    stageEval_climb_ne_zero n hT i h (stagePoint n i) hmem
  rw [T.climb_succ h, hT i]
  exact isFull_connect_of_stageEval_ne_zero n i hb

end Gen

/-! ### The `n = 2` instance -/

/-- The fibre value of a section depends continuously on the point. -/
theorem continuous_stageEval (k : ℕ) (a : StageAlgebra k) :
    Continuous fun w : baseX k => stageEval k w a := Gen.continuous_stageEval 2 k a

/-- The set of points at which a section does not vanish is open. -/
theorem isOpen_stageEval_ne_zero (k : ℕ) (a : StageAlgebra k) :
    IsOpen ((fun w : baseX k => stageEval k w a) ⁻¹'
      {(0 : Matrix (EIdx k) (EIdx k) ℂ)}ᶜ) :=
  Gen.isOpen_stageEval_ne_zero 2 k a

/-- **Nonvanishing travels up the tower.** -/
theorem stageEval_climb_ne_zero {T : LIX.CStarTower StageAlgebra}
    (hT : ∀ i, T.succHom i = connect i) {k : ℕ} {a : StageAlgebra k} :
    ∀ (i : ℕ) (h : k ≤ i) (w : baseX i),
      stageEval k (basePr h w) a ≠ 0 → stageEval i w (T.climb i k a) ≠ 0 :=
  Gen.stageEval_climb_ne_zero 2 hT

/-- **Stagewise fullness.**  For every nonzero `a ∈ A_k` there is `j ≥ k` with `φ_{k,j}(a)`
full in `A_j`.

This is the hypothesis of `LIX.CStarTower.isSimpleCStar_limit_of_ne_zero`, in its exact binder
shape: `(k : ℕ) (a : StageAlgebra k)`, then `a ≠ 0`, then `∃ j, k ≤ j ∧ IsFull (T.climb j k a)`,
stated over the raw recursion `T.climb` with the target index first. -/
theorem isFull_climb_of_ne_zero {T : LIX.CStarTower StageAlgebra}
    (hT : ∀ i, T.succHom i = connect i) (k : ℕ) (a : StageAlgebra k) (hne : a ≠ 0) :
    ∃ j, k ≤ j ∧ GroupApproximation.LIX.IsFull (T.climb j k a) :=
  Gen.isFull_climb_of_ne_zero 2 hT k a hne

end

end STW59
end GroupApproximation
