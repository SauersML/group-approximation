import GroupApproximation.Sofic.GreendlingerBetaBranch
import GroupApproximation.Sofic.GreendlingerDehn

/-!
# L-red, proved: the (β) coincidence cannot happen in a reduced palindrome

`GreendlingerBetaBranch` names `ReducednessVoidsCoincidence` as the statement
that, in the conjugator-overrun regime, the head rotation inverted is never the
rotation of the landing rotation that the overrun aligns against.  This file
proves it, so the predicate is inhabited and its consumers become
unconditional.

The argument is four steps and spends nothing but reducedness.

The alignment says the last `i` letters of the head conjugator `c` are the
first `i` letters of the landing rotation `t'`, so `t'.take i` ends with `c`'s
last letter `x`.  Rotating `t'` by `i` moves exactly that block to the back, so
`t'.rotate i` ends with `x` too.  If the coincidence held, `invRev t` would end
with `x` — but `invRev (y :: t₁) = invRev t₁ ++ [invLetter y]`, so `invRev t`
ends with the inversion of `t`'s *first* letter.  Hence `t` begins with
`invLetter x`, and

    palindrome c t = c₀ ++ (x :: invLetter x :: t₁ ++ invRev c)

sets a letter beside its own inverse, which `not_isReduced_cancel` forbids.

Nothing here is small cancellation and nothing is minimality: it is the mirror
symmetry of the palindrome against a rotation, and the whole content is that a
rotation by `i` puts the `i`-th letter last.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-- **The last block of a rotation.**  If a word's first `i` letters end with
`x`, so does its rotation by `i`: the rotation moves that block to the back. -/
theorem rotate_eq_append_singleton {t' z : List (α × Bool)} {x : α × Bool}
    {i : ℕ} (hi : i ≤ t'.length) (htake : t'.take i = z ++ [x]) :
    t'.rotate i = (t'.drop i ++ z) ++ [x] := by
  rw [List.rotate_eq_drop_append_take hi, htake]
  simp only [List.append_assoc]

/-- **L-red.**  In the conjugator-overrun regime the coincidence is void, and
reducedness of the head palindrome alone refutes it. -/
theorem reducednessVoidsCoincidence [DecidableEq α] :
    ReducednessVoidsCoincidence α := by
  intro c t t' i hpal hi hic halign hcoin
  -- the aligned block, of length exactly `i`
  set k := c.length - i with hk
  have hdlen : (c.drop k).length = i := by
    rw [List.length_drop]
    omega
  -- `t` is nonempty: otherwise the coincidence empties `t'` and the block
  have htne : t ≠ [] := by
    intro hnil
    rw [hnil] at hcoin
    have h1 : t'.rotate i = [] := by rw [← hcoin]; simp
    have h2 : t' = [] := List.rotate_eq_nil_iff.mp h1
    rw [h2] at halign
    have h3 : c.drop k = [] := List.prefix_nil.mp halign
    rw [h3] at hdlen
    simp at hdlen
    omega
  -- `c` is nonempty, and splits off its last letter
  have hcne : c ≠ [] := by
    intro hnil
    rw [hnil] at hic
    simp at hic
    omega
  obtain ⟨y, t₁, rfl⟩ : ∃ y t₁, t = y :: t₁ := by
    cases t with
    | nil => exact absurd rfl htne
    | cons y t₁ => exact ⟨y, t₁, rfl⟩
  set x := c.getLast hcne with hx
  have hcsplit : c.dropLast ++ [x] = c := List.dropLast_append_getLast hcne
  -- the aligned block ends with `x`
  have hkle : k ≤ c.dropLast.length := by
    have := List.length_dropLast (l := c)
    omega
  have hdrop : c.drop k = c.dropLast.drop k ++ [x] := by
    conv_lhs => rw [← hcsplit]
    rw [drop_append_of_le k c.dropLast [x] hkle]
  -- the alignment identifies it with `t'.take i`
  have hile : i ≤ t'.length := by
    have h1 := halign.length_le
    omega
  have htake : t'.take i = c.dropLast.drop k ++ [x] := by
    have h := List.prefix_iff_eq_take.mp halign
    rw [hdlen] at h
    rw [← h, hdrop]
  -- so the rotation ends with `x`, and the coincidence forces `t`'s head
  have hrot := rotate_eq_append_singleton hile htake
  have hinv : FreeGroup.invRev t₁ ++ [invLetter y]
      = (t'.drop i ++ c.dropLast.drop k) ++ [x] := by
    rw [← hrot, ← hcoin, invRev_cons]
  have hlast : invLetter y = x := by
    have h := (List.append_inj' hinv rfl).2
    simpa using h
  have hy : y = invLetter x := by
    rw [← hlast, invLetter_invLetter]
  -- the palindrome now carries a letter beside its inverse
  have hsplit : palindrome c (y :: t₁)
      = c.dropLast ++ (x :: invLetter x :: (t₁ ++ FreeGroup.invRev c)) := by
    unfold palindrome
    conv_lhs => rw [← hcsplit]
    rw [hy]
    simp only [List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append]
  rw [hsplit] at hpal
  exact not_isReduced_cancel hpal

/-- The (β) coincidence discharge, unconditional: the predicate is inhabited,
so `GreendlingerBetaBranch.invRev_ne_rotate_of_reduced` no longer needs its
gate hypothesis. -/
theorem invRev_ne_rotate_of_isReduced [DecidableEq α]
    {c t t' : List (α × Bool)} {i : ℕ}
    (hpal : FreeGroup.IsReduced (palindrome c t))
    (hi : 0 < i) (hic : i ≤ c.length)
    (halign : c.drop (c.length - i) <+: t') :
    FreeGroup.invRev t ≠ t'.rotate i :=
  reducednessVoidsCoincidence c t t' i hpal hi hic halign

end SmallCancellationRouter
end GroupApproximation
