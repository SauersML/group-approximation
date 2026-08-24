import GroupApproximation.Sofic.GreendlingerWeight

/-!
# Minimality forbids a cancelling pair of factors

The curvature count over `ConjExprMatching`'s labelled matching needs the
diagram to be **reduced**: no two regions may be glued so that they cancel each
other.  Nothing in the matching machinery supplies that ---
`ConjExprMatching.exists_dtree_labelledWord` asks only that the expression
spells `w`, and the classical curvature lemma is false without reducedness ---
so it has to come from the expression, and the only thing the expression carries
is `IsMinimalConjExpr`.

This file spends it.

## The statement

Write a conjugate-product expression as

```text
    A ++ (c₁, s₁) :: (B ++ (c₂, s₂) :: C)
```

so that `(c₁, s₁)` and `(c₂, s₂)` are any two of its factors and `B` is whatever
stands between them.  The two factors *cancel* exactly when the first is the
inverse of the second conjugated across the intervening product:

```text
    c₁ (s₁) c₁⁻¹  =  (conjEval B) (c₂ (s₂) c₂⁻¹)⁻¹ (conjEval B)⁻¹
```

`not_cancelling_pair_of_minimal` says a minimal expression admits no such pair.

## Why it is this cheap

The obvious route --- move the second factor leftwards past the intervening ones
by `x y = y (y⁻¹ x y)`, then delete the adjacent inverse pair --- is not needed,
and neither is any re-conjugation.  The cancellation hypothesis already collapses
the middle of the product on the nose:

```text
    P₁ · (conjEval B) · P₂
      = (conjEval B) P₂⁻¹ (conjEval B)⁻¹ · (conjEval B) · P₂
      = conjEval B
```

so deleting *both* factors and keeping `B` where it is leaves the value
unchanged.  `ConjValid` is `∀ x ∈ e, x.2 ∈ symmetrization R`, a pointwise
condition, so it survives deletion for free.  What is left is an expression for
the same `g` with two fewer factors, and length is the *first* of the two
well-orderings `IsMinimalConjExpr` minimises --- so the weight half is never
touched and the contradiction is immediate.

## What it does not say

Nothing about pieces, small cancellation or the constant.  It is a statement
about minimal expressions alone, and it is the reduced-diagram hypothesis the
count should take, in whatever shape the count finds convenient:
`not_cancelling_pair_of_minimal` is the general two-factor form,
`not_adjacent_cancelling_pair_of_minimal` the adjacent one (`B = []`), and
`ne_inv_conj_of_minimal` the same fact stated as an inequation between the two
regions' labels.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*} [DecidableEq α]

/-- The element one factor of a conjugate-product expression contributes. -/
def factorValue (c : FreeGroup α) (s : List (α × Bool)) : FreeGroup α :=
  c * FreeGroup.mk s * c⁻¹

omit [DecidableEq α] in
@[simp] theorem conjEval_cons_factorValue (c : FreeGroup α)
    (s : List (α × Bool)) (e : List (FreeGroup α × List (α × Bool))) :
    conjEval ((c, s) :: e) = factorValue c s * conjEval e := rfl

omit [DecidableEq α] in
/-- Deleting factors preserves validity, which is a pointwise condition. -/
theorem conjValid_of_subset {R : Set (List (α × Bool))}
    {e e' : List (FreeGroup α × List (α × Bool))}
    (h : ConjValid R e) (hsub : ∀ x ∈ e', x ∈ e) : ConjValid R e' :=
  fun x hx => h x (hsub x hx)

/-- **A minimal expression has no cancelling pair of factors.**

If the factor `(c₁, s₁)` is the inverse of the factor `(c₂, s₂)` conjugated
across everything between them, both may be deleted with the intervening block
left in place, giving a valid expression for the same element with two fewer
factors.  Minimal length forbids it. -/
theorem not_cancelling_pair_of_minimal {R : Set (List (α × Bool))}
    {g : FreeGroup α} {A B C : List (FreeGroup α × List (α × Bool))}
    {c₁ c₂ : FreeGroup α} {s₁ s₂ : List (α × Bool)}
    (hmin : IsMinimalConjExpr R
      (A ++ (c₁, s₁) :: (B ++ (c₂, s₂) :: C)) g) :
    factorValue c₁ s₁ ≠
      conjEval B * (factorValue c₂ s₂)⁻¹ * (conjEval B)⁻¹ := by
  intro hcan
  obtain ⟨hvalid, heval, hlen, -⟩ := hmin
  have hsub : ∀ x ∈ A ++ (B ++ C), x ∈ A ++ (c₁, s₁) :: (B ++ (c₂, s₂) :: C) := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_left _ h
    · refine List.mem_append_right _ ?_
      rcases List.mem_append.mp h with h' | h'
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ h')
      · exact List.mem_cons_of_mem _
          (List.mem_append_right _ (List.mem_cons_of_mem _ h'))
  have hvalid' : ConjValid R (A ++ (B ++ C)) :=
    conjValid_of_subset hvalid hsub
  have hmid : factorValue c₁ s₁ * (conjEval B * (factorValue c₂ s₂ * conjEval C))
      = conjEval B * conjEval C := by
    rw [hcan]
    group
  have hkey : conjEval (A ++ (c₁, s₁) :: (B ++ (c₂, s₂) :: C))
      = conjEval (A ++ (B ++ C)) := by
    simp only [conjEval_append, conjEval_cons_factorValue]
    rw [hmid]
  have heval' : conjEval (A ++ (B ++ C)) = g := hkey ▸ heval
  have hb := hlen (A ++ (B ++ C)) hvalid' heval'
  simp only [List.length_append, List.length_cons] at hb
  omega

/-- **The adjacent case**, which is the shape the descent's own
`GreendlingerRegime.mk_palindrome_mul_ne_one_of_minimal` covers: two
neighbouring factors of a minimal expression are not mutually inverse. -/
theorem not_adjacent_cancelling_pair_of_minimal {R : Set (List (α × Bool))}
    {g : FreeGroup α} {A C : List (FreeGroup α × List (α × Bool))}
    {c₁ c₂ : FreeGroup α} {s₁ s₂ : List (α × Bool)}
    (hmin : IsMinimalConjExpr R (A ++ (c₁, s₁) :: (c₂, s₂) :: C) g) :
    factorValue c₁ s₁ * factorValue c₂ s₂ ≠ 1 := by
  intro hcan
  refine not_cancelling_pair_of_minimal (A := A) (B := []) (C := C)
    (by simpa using hmin) ?_
  rw [conjEval_nil]
  have : factorValue c₂ s₂ = (factorValue c₁ s₁)⁻¹ := by
    rw [← mul_left_cancel_iff (a := factorValue c₁ s₁), hcan, mul_inv_cancel]
  rw [this]
  group

/-- **The reduced-diagram condition, as an inequation between two regions.**

Read in the picture: the region `(c₁, s₁)` and the region `(c₂, s₂)` are not
mirror images glued so as to cancel.  This is the hypothesis a curvature count
should take; it is supplied here from minimality alone, with no small
cancellation input. -/
theorem ne_inv_conj_of_minimal {R : Set (List (α × Bool))}
    {g : FreeGroup α} {A B C : List (FreeGroup α × List (α × Bool))}
    {c₁ c₂ : FreeGroup α} {s₁ s₂ : List (α × Bool)}
    (hmin : IsMinimalConjExpr R
      (A ++ (c₁, s₁) :: (B ++ (c₂, s₂) :: C)) g) :
    (conjEval B)⁻¹ * factorValue c₁ s₁ * conjEval B * factorValue c₂ s₂ ≠ 1 := by
  intro hcan
  refine not_cancelling_pair_of_minimal (A := A) (B := B) (C := C) hmin ?_
  have h2 : (conjEval B)⁻¹ * factorValue c₁ s₁ * conjEval B
      = (factorValue c₂ s₂)⁻¹ := by
    have hmul := congrArg (fun x => x * (factorValue c₂ s₂)⁻¹) hcan
    simpa [mul_assoc] using hmul
  calc factorValue c₁ s₁
      = conjEval B * ((conjEval B)⁻¹ * factorValue c₁ s₁ * conjEval B)
          * (conjEval B)⁻¹ := by group
    _ = conjEval B * (factorValue c₂ s₂)⁻¹ * (conjEval B)⁻¹ := by rw [h2]

end SmallCancellationRouter
end GroupApproximation
