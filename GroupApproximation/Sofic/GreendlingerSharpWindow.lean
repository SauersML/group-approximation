import GroupApproximation.Sofic.GreendlingerDeepTailWindow

/-!
# The sharp window layer

`GreendlingerDeepTailWindow` carries the window architecture at the constant
`λ = 1/6`, where `1 - 3λ = 1/2` and every bound can be written with natural
number arithmetic: a window longer than half its rotation, two pieces each
shorter than a sixth, and `omega` to connect them.  The sharp residuals of
`GreendlingerSharpResidualWiring` need the same architecture at an arbitrary
`λ ≤ 1/6`, where `1 - 3λ ≥ 1/2` and the bounds are rational.

The rotation-window producer is already twinned:
`greendlingerAtSharp_of_rotation_window` proves `GreendlingerAtSharp` from a
window satisfying `(1 - 3λ)|t₃| < m`.  What was missing is everything that
*feeds* it — the two-piece survivor count and the window predicate itself.
This file supplies exactly that, mirroring the `λ`-free file statement for
statement.

## The arithmetic, and why `1 - 3λ` is not tight here

The two-piece count is generous.  If the landing rotation loses `i` letters at
the front and `k` at the back, and each loss is a piece, then `C'(λ)` gives
`i, k < λ|t₃|`, so the survivor exceeds `(1 - 2λ)|t₃|`.  Greendlinger's
conclusion only asks for `(1 - 3λ)|t₃|`, and `(1 - 3λ) ≤ (1 - 2λ)` whenever
`λ ≥ 0`, so a whole `λ|t₃|` of slack is left over.  That slack is why the
`λ`-free file could afford to phrase the same step as "a sixth plus a sixth is
comfortably inside a half": at `λ = 1/6` the two-piece bound gives `2/3` where
only `1/2` is required.

`sharp_survivor_of_two_pieces` is that observation and nothing more.  It is the
sharp twin of `two_mul_lt_of_two_pieces`, whose proof is `omega`.

## What this does and does not close

`deepOverrunLandingSharp_of_windowSharp` reduces the open residual
`DeepOverrunLandingSharp` to `DeepOverrunWindowSharp`, exactly as
`deepOverrunLanding_of_window` reduces `DeepOverrunLanding` to
`DeepOverrunWindow`.  Both window predicates are still `def`s, not theorems:
neither the `λ`-free one nor this twin is produced anywhere, so this is a
reduction of an open statement to a more elementary open statement, not a
discharge of it.  The gain is that the target no longer mentions
`GreendlingerAtSharp`, relator membership, or rotations: it is a statement
about where two cancellations leave a window inside one word.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The sharp two-piece survivor count -/

/-- **Two pieces leave more than `1 - 3λ`.**  The sharp twin of
`two_mul_lt_of_two_pieces`.

A rotation eaten by fewer than `λ|t₃|` letters at each end retains more than
`(1 - 2λ)|t₃|`, and `(1 - 3λ)|t₃| ≤ (1 - 2λ)|t₃|` because `λ|t₃| ≥ 0`.  The
`λ`-free version is the case `λ = 1/6` with both sides cleared of
denominators, which is why it is discharged by `omega` and this is not. -/
theorem sharp_survivor_of_two_pieces {t₃ : List (α × Bool)} {i k : ℕ}
    {lam : ℚ} (hlam : 0 ≤ lam) (hik : i + k ≤ t₃.length)
    (hi : (i : ℚ) < lam * (t₃.length : ℚ))
    (hk : (k : ℚ) < lam * (t₃.length : ℚ)) :
    (1 - 3 * lam) * (t₃.length : ℚ) < ((t₃.length - i - k : ℕ) : ℚ) := by
  have hi' : i ≤ t₃.length := by omega
  have hk' : k ≤ t₃.length - i := by omega
  have hcast : ((t₃.length - i - k : ℕ) : ℚ)
      = (t₃.length : ℚ) - (i : ℚ) - (k : ℚ) := by
    rw [Nat.cast_sub hk', Nat.cast_sub hi']
  have hnn : (0 : ℚ) ≤ lam * (t₃.length : ℚ) :=
    mul_nonneg hlam (by exact_mod_cast Nat.zero_le t₃.length)
  rw [hcast]
  nlinarith [hi, hk, hnn]

/-! ## 2.  The sharp window producer -/

/-- **The sharp arc, from the two piece bounds alone.**  The sharp twin of
`greendlingerAt_of_two_piece_window`.

Same shape, same two hypotheses, with each piece bound stated against `λ|t₃|`
rather than against a sixth of `|t₃|`.  The window length is written as
`|t₃| - i - k`, so the fit condition is arithmetic and the arc condition is
`sharp_survivor_of_two_pieces`. -/
theorem greendlingerAtSharp_of_two_piece_window {R : Set (List (α × Bool))}
    {lam : ℚ} {t₃ w A C : List (α × Bool)} {i k n : ℕ}
    (hlam : 0 ≤ lam)
    (ht₃ : t₃ ∈ symmetrization R)
    (hw : w = A ++ (t₃.drop i).take (t₃.length - i - k) ++ C)
    (hn : n ≤ A.length)
    (hik : i + k ≤ t₃.length)
    (hi : (i : ℚ) < lam * (t₃.length : ℚ))
    (hk : (k : ℚ) < lam * (t₃.length : ℚ)) :
    GreendlingerAtSharp R lam n w :=
  greendlingerAtSharp_of_rotation_window ht₃ hw hn (by omega)
    (sharp_survivor_of_two_pieces hlam hik hi hk)

/-! ## 3.  The sharp window predicate, and the reduction it buys -/

/-- **The sharp twin of `DeepOverrunWindow`.**

Every structural field is quoted verbatim from the `λ`-free predicate; only
the offset hypothesis and the window bound move, exactly as they do between
`DeepOverrunLanding` and `DeepOverrunLandingSharp`.  The conclusion asks for a
window of the landing rotation longer than `(1 - 3λ)` of it, beginning at or
after the required offset. -/
def DeepOverrunWindowSharp [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t c₂ t₂ c₃ t₃ M B' : List (α × Bool))
    (f : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α) (j N : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂)
      :: (FreeGroup.mk c₃, t₃) :: f) g →
    t ∈ symmetrization R → t₂ ∈ symmetrization R → t₃ ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    FreeGroup.IsReduced (palindrome c₂ t₂) →
    FreeGroup.IsReduced (palindrome c₃ t₃) →
    M <:+ palindrome c t →
    (conjEval ((FreeGroup.mk c₂, t₂)
      :: (FreeGroup.mk c₃, t₃) :: f)).toWord = FreeGroup.invRev M ++ B' →
    ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂) →
    B' = (conjEval ((FreeGroup.mk c₃, t₃) :: f)).toWord.drop N →
    c.length < M.length → (j : ℚ) < lam * (t.length : ℚ) →
    c.length + t.length < M.length + j →
    ∃ (A C : List (α × Bool)) (i m : ℕ),
      B' = A ++ (t₃.drop i).take m ++ C ∧
        M.length + j - (c.length + t.length) ≤ A.length ∧
        i + m ≤ t₃.length ∧ (1 - 3 * lam) * (t₃.length : ℚ) < (m : ℚ)

/-- **The sharp landing obligation, from the sharp window.**

The sharp twin of `deepOverrunLanding_of_window`, and the same one-line proof:
the window is destructured and handed to the rotation-window producer, which is
already twinned.  Nothing about the deep regime is re-examined, because the
`λ`-free reduction did not examine it either.

This does not discharge `DeepOverrunLandingSharp`; it moves it to
`DeepOverrunWindowSharp`, which mentions no relator bookkeeping. -/
theorem deepOverrunLandingSharp_of_windowSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (h : DeepOverrunWindowSharp R lam) :
    DeepOverrunLandingSharp R lam := by
  intro c t c₂ t₂ c₃ t₃ M B' f g j N hmin ht ht₂ ht₃ hredp hredp₂ hredp₃ hMsuf
    hword hover hB' hlow hj hgt
  obtain ⟨A, C, i, m, hsplit, hn, hfit, hbound⟩ :=
    h c t c₂ t₂ c₃ t₃ M B' f g j N hmin ht ht₂ ht₃ hredp hredp₂ hredp₃ hMsuf
      hword hover hB' hlow hj hgt
  exact greendlingerAtSharp_of_rotation_window ht₃ hsplit hn hfit hbound

end SmallCancellationRouter
end GroupApproximation
