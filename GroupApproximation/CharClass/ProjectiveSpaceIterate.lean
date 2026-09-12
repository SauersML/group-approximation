import GroupApproximation.CharClass.ProjectiveSpaceStable

/-!
# The iterated hyperplane inclusion, and stability of the generator along it

`pull_cpIncl_cpGen` says the one-step hyperplane inclusion carries the degree-two
generator to the degree-two generator.  Comparing `ℂP^d` with `ℂP^N` for `N` far
above `d`, which is what stabilising a bundle does, needs the same for the
`k`-fold inclusion, and that is a two-line induction.

No degree transport appears: `d + (k + 1)` reduces to `(d + k) + 1`, so each step
of the iterate typechecks against the one-step lemma with nothing to cast.

## Main declarations

* `cpInclIter` — the `k`-fold hyperplane inclusion `ℂP^d ⊆ ℂP^{d+k}`.
* `pull_cpInclIter_cpGen` — **generator stability along it**.
* `pull_cpInclIter_cupPowE` — and along the powers.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory

noncomputable section

/-- The `k`-fold hyperplane inclusion `ℂP^d ⊆ ℂP^{d+k}`. -/
def cpInclIter (d : ℕ) : (k : ℕ) → (CPtop d ⟶ CPtop (d + k))
  | 0 => 𝟙 (CPtop d)
  | (k + 1) => cpInclIter d k ≫ cpIncl (d + k)

@[simp] theorem cpInclIter_zero (d : ℕ) : cpInclIter d 0 = 𝟙 (CPtop d) := rfl

@[simp] theorem cpInclIter_succ (d k : ℕ) :
    cpInclIter d (k + 1) = cpInclIter d k ≫ cpIncl (d + k) := rfl

/-- **Stability of the degree-two generator along the iterated inclusion.** -/
theorem pull_cpInclIter_cpGen (d : ℕ) (hd : 1 ≤ d) (k : ℕ) :
    pull (cpInclIter d k) 2 (cpGen (d + k) (by omega)) = cpGen d hd := by
  induction k with
  | zero => exact pull_id 2 (cpGen d hd)
  | succ k ih =>
    show pull (cpInclIter d k ≫ cpIncl (d + k)) 2 (cpGen (d + k + 1) (by omega))
      = cpGen d hd
    rw [pull_comp, pull_cpIncl_cpGen (d + k) (by omega), ih]

/-- The powers are stable along it too. -/
theorem pull_cpInclIter_cupPowE (d : ℕ) (hd : 1 ≤ d) (k m : ℕ) :
    pull (cpInclIter d k) (2 * m) (cupPowE (cpGen (d + k) (by omega)) m)
      = cupPowE (cpGen d hd) m := by
  rw [pull_cupPowE, pull_cpInclIter_cpGen d hd k]

end

end CPn
end CharClass
end GroupApproximation
