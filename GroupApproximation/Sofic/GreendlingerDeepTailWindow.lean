import GroupApproximation.Sofic.GreendlingerDeepInduction

/-!
# The landing arc over an arbitrary tail

`GreendlingerDeepThreeFactor` produces the landing arc where the landing factor
is the **last** one, because there the surviving word is a suffix of a single
palindrome and the arc is a suffix of that palindrome's rotation.
`GreendlingerDeepInduction.exists_overrun_landing_drop` removes the three-factor
hypothesis from the decomposition: for any tail `T` an overrun leaves

    B' = (conjEval T).toWord.drop N.

This file removes it from the *producer* as well, which is what makes
`GreendlingerDeepInduction.DeepOverrunLandingTail` unnecessary.

## Why the producer had to move

Over a longer tail the landing rotation is eaten from **both** ends.  The head's
block eats `i` letters off its front, exactly as before; but the landing factor's
own block now eats `k` letters off its back, because what survives of
`palindrome c₃ t₃` in `(conjEval ((mk c₃, t₃) :: f)).toWord` is only the prefix
`P₃` that the next cancellation leaves.  At `f = []` there is no next
cancellation, `P₃` is the whole palindrome and `k = 0` — which is why the
one-sided producer sufficed at three factors and only there.

So the arc is a **window** of the rotation rather than a suffix of it, and the
condition becomes symmetric:

    2 · (i + k) < |t₃|,

with the window `(t₃.drop i).take m` of length `m = |t₃| − i − k`.  At `k = 0`
this is `2i < |t₃|`, the bound
`GreendlingerDeepThreeFactor.greendlingerAt_of_landing_start` already pays for
out of the piece bound alone.

`greendlingerAt_of_rotation_window` is that producer.  It names neither the
eaten stretch `E` nor the head rotation, so — like the landing-start lemma it
generalizes — it is untouched by the swallow question: it holds whether or not
`M = E ++ invRev c` is available, and whether or not `|M| ≤ |c| + |t|`.

## What is left

`DeepOverrunWindow`: the overrun configuration exhibits such a window, late
enough.  `deepOverrunLanding_of_window` discharges
`GreendlingerDeepInduction.DeepOverrunLanding` from it in one step, with **no
case split on the tail** — so the three-factor count and the not-last-factor
residual are replaced by a single statement covering both.

The step this file does not take is turning the frame's `P₃` into the window
explicitly: from `palindrome c₃ t₃ = P₃ ++ M₃` and `N ≤ |P₃|`, the surviving
word is `P₃.drop N ++ B₃` and the window is `(t₃.drop i).take m` sitting inside
`P₃.drop N` after `c₃.drop N`.  `take_drop_swap` below is the commutation that
step needs; it is proved here rather than cited because the argument should not
depend on guessing a library name.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  Commuting a take past a drop -/

/-- **A window read either way round.**  Taking `a` letters and then dropping
`b` is dropping `b` and then taking `a − b`.

Mathlib states the neighbouring identities for `take` against `append` and for
`drop` against `drop`; the descent needs this one, and proving it here keeps the
window arithmetic free of any dependence on a library name. -/
theorem take_drop_swap {β : Type*} :
    ∀ (b a : ℕ) (l : List β), (l.take a).drop b = (l.drop b).take (a - b) := by
  intro b
  induction b with
  | zero =>
      intro a l
      rw [List.drop_zero, List.drop_zero, Nat.sub_zero]
  | succ b ih =>
      intro a l
      cases l with
      | nil => simp
      | cons x xs =>
          cases a with
          | zero => simp
          | succ a =>
              rw [List.take_succ_cons, List.drop_succ_cons,
                List.drop_succ_cons, ih a xs]
              congr 1
              omega

/-! ## 2.  The arc from a window of the landing rotation -/

/-- **The two-sided landing arc.**  A contiguous window of a symmetrized
rotation, longer than half of it, is a Greendlinger arc wherever it sits.

This supersedes `GreendlingerDeepThreeFactor.greendlingerAt_of_landing_start`
and `greendlingerAt_of_landing_intrusion`, both of which take the window to run
to the end of the rotation — the case `i + m = |t₃|`, which is what a *last*
landing factor produces.  Over a longer tail the landing factor's own block
truncates the window on the right as well, and only the length of the window
matters.

Names neither the eaten stretch nor the head rotation, so no orientation
package and no swallow bound are needed to apply it. -/
theorem greendlingerAt_of_rotation_window {R : Set (List (α × Bool))}
    {t₃ w A C : List (α × Bool)} {i m n : ℕ}
    (ht₃ : t₃ ∈ symmetrization R)
    (hw : w = A ++ (t₃.drop i).take m ++ C)
    (hn : n ≤ A.length)
    (hfit : i + m ≤ t₃.length)
    (hbound : t₃.length < 2 * m) :
    GreendlingerAt R n w := by
  refine ⟨A, (t₃.drop i).take m, C, hw, hn, t₃.rotate i,
    rotate_mem_symmetrization ht₃ i, ?_, ?_⟩
  · rw [List.rotate_eq_drop_append_take (show i ≤ t₃.length by omega)]
    exact (List.take_prefix m (t₃.drop i)).trans ⟨t₃.take i, rfl⟩
  · rw [List.length_rotate, List.length_take, List.length_drop]
    omega

/-- **The sharp twin.**  The same window against `(1 − 3λ)`, where the condition
reads `i + k < 3λ|t₃|` once the window length is written as `|t₃| − i − k`. -/
theorem greendlingerAtSharp_of_rotation_window {R : Set (List (α × Bool))}
    {lam : ℚ} {t₃ w A C : List (α × Bool)} {i m n : ℕ}
    (ht₃ : t₃ ∈ symmetrization R)
    (hw : w = A ++ (t₃.drop i).take m ++ C)
    (hn : n ≤ A.length)
    (hfit : i + m ≤ t₃.length)
    (hbound : (1 - 3 * lam) * (t₃.length : ℚ) < (m : ℚ)) :
    GreendlingerAtSharp R lam n w := by
  refine ⟨A, (t₃.drop i).take m, C, hw, hn, t₃.rotate i,
    rotate_mem_symmetrization ht₃ i, ?_, ?_⟩
  · rw [List.rotate_eq_drop_append_take (show i ≤ t₃.length by omega)]
    exact (List.take_prefix m (t₃.drop i)).trans ⟨t₃.take i, rfl⟩
  · have hlen : ((t₃.drop i).take m).length = m := by
      rw [List.length_take, List.length_drop]
      omega
    rw [List.length_rotate, hlen]
    exact hbound

/-! ## 3.  The residual, over an arbitrary tail -/

/-- **The overrun exhibits a window of the landing rotation, late enough.**

Every field is quoted from `GreendlingerDeepInduction.DeepOverrunLanding`; only
the conclusion changes, from "there is an arc" to "there is a window of `t₃`
longer than half of it, beginning at or after the required offset".  That is a
statement about where the two cancellations leave the landing rotation, with the
relator bookkeeping already discharged by
`greendlingerAt_of_rotation_window`. -/
def DeepOverrunWindow [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
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
    c.length < M.length → 6 * j < t.length →
    c.length + t.length < M.length + j →
    ∃ (A C : List (α × Bool)) (i m : ℕ),
      B' = A ++ (t₃.drop i).take m ++ C ∧
        M.length + j - (c.length + t.length) ≤ A.length ∧
        i + m ≤ t₃.length ∧ t₃.length < 2 * m

/-- **The landing obligation, from the window, with no case split on the tail.**

`GreendlingerDeepInduction.deepOverrunLanding_of_depth_of_tail` splits on
whether the landing factor is the last, spending
`GreendlingerDeepThreeFactor.DeepOverrunDepth` on one branch and leaving
`DeepOverrunLandingTail` on the other.  This discharges both at once: the window
is what each branch was separately arranging, and the producer does not care how
long the tail is.

So `DeepOverrunLandingTail` is no longer needed on this route. -/
theorem deepOverrunLanding_of_window [DecidableEq α]
    {R : Set (List (α × Bool))} (h : DeepOverrunWindow R) :
    DeepOverrunLanding R := by
  intro c t c₂ t₂ c₃ t₃ M B' f g j N hmin ht ht₂ ht₃ hredp hredp₂ hredp₃ hMsuf
    hword hover hB' hlow hj hgt
  obtain ⟨A, C, i, m, hsplit, hn, hfit, hbound⟩ :=
    h c t c₂ t₂ c₃ t₃ M B' f g j N hmin ht ht₂ ht₃ hredp hredp₂ hredp₃ hMsuf
      hword hover hB' hlow hj hgt
  exact greendlingerAt_of_rotation_window ht₃ hsplit hn hfit hbound

/-- **`DeepOverrunArc` over the window alone.**  Composing with the frame's own
reduction: the deep regime now costs one statement about where the two
cancellations leave the landing rotation. -/
theorem deepOverrunArc_of_window [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (h : DeepOverrunWindow R) : DeepOverrunArc R :=
  deepOverrunArc_of_landing hR hRne (deepOverrunLanding_of_window h)

end SmallCancellationRouter
end GroupApproximation
