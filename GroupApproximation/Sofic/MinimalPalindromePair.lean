import GroupApproximation.Sofic.MinimalNoCancellingPair
import GroupApproximation.Sofic.GreendlingerNormalForm

/-!
# The no-cancelling-pair condition in palindrome vocabulary

`Sofic/MinimalNoCancellingPair` proves that a minimal conjugate-product
expression admits no pair of factors that cancel across the intervening product.
It states that over `factorValue c s = c · s · c⁻¹`, because that is the shape
`conjEval` is defined in.  The rest of the Greendlinger lane speaks
*palindromes*: `palindrome c t = c ++ t ++ invRev c`, with
`GreendlingerNormalForm.mk_palindrome` the bridge.  This file restates the
condition there, so the count and the descent can quote the same fact.

## What it gives

`GreendlingerRegime.mk_palindrome_mul_ne_one_of_minimal` already says that two
*adjacent* factors of a minimal expression do not spell mutually inverse
elements.  `mk_palindrome_mul_ne_one_of_minimal_pair` below is the same for
*any* two factors, with the intervening block `B` conjugating the second:

```text
    mk (palindrome c₁ t₁) · (conjEval B) · mk (palindrome c₂ t₂) · (conjEval B)⁻¹ ≠ 1
```

At `B = []` it is the adjacent statement, recovered as
`mk_palindrome_mul_ne_one_of_minimal_adjacent`, which is why the two do not have
to be proved twice.

## Why the general form is the one the count needs

The descent walks factors in order, so adjacency is all it ever sees.  A
curvature count does not: two regions of the diagram may be far apart in the
expression and still share an edge, and the reducedness the count needs is that
*those* two do not cancel.  The intervening product is exactly the conjugator
that carries one region to where it meets the other.

No small cancellation input, no constant, no hypothesis beyond minimality.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- `factorValue` on a free-group generator conjugator is the palindrome's
element.  This is `GreendlingerNormalForm.mk_palindrome` read backwards. -/
theorem factorValue_mk (c t : List (α × Bool)) :
    factorValue (FreeGroup.mk c) t = FreeGroup.mk (palindrome c t) := by
  rw [mk_palindrome]
  rfl

/-- **No two factors of a minimal expression cancel**, in palindrome
vocabulary.  The general form: the two factors may sit anywhere, and `B` is
whatever stands between them. -/
theorem mk_palindrome_mul_ne_one_of_minimal_pair {R : Set (List (α × Bool))}
    {g : FreeGroup α} {A B C : List (FreeGroup α × List (α × Bool))}
    {c₁ c₂ t₁ t₂ : List (α × Bool)}
    (hmin : IsMinimalConjExpr R
      (A ++ (FreeGroup.mk c₁, t₁) :: (B ++ (FreeGroup.mk c₂, t₂) :: C)) g) :
    FreeGroup.mk (palindrome c₁ t₁) * conjEval B
        * FreeGroup.mk (palindrome c₂ t₂) * (conjEval B)⁻¹ ≠ 1 := by
  intro hcan
  refine not_cancelling_pair_of_minimal (A := A) (B := B) (C := C) hmin ?_
  rw [factorValue_mk, factorValue_mk]
  have key : FreeGroup.mk (palindrome c₁ t₁)
      * (conjEval B * FreeGroup.mk (palindrome c₂ t₂) * (conjEval B)⁻¹) = 1 := by
    rw [← hcan]; group
  calc FreeGroup.mk (palindrome c₁ t₁)
      = FreeGroup.mk (palindrome c₁ t₁)
          * (conjEval B * FreeGroup.mk (palindrome c₂ t₂) * (conjEval B)⁻¹)
          * (conjEval B * FreeGroup.mk (palindrome c₂ t₂) * (conjEval B)⁻¹)⁻¹ := by
            group
    _ = (conjEval B * FreeGroup.mk (palindrome c₂ t₂) * (conjEval B)⁻¹)⁻¹ := by
          rw [key, one_mul]
    _ = conjEval B * (FreeGroup.mk (palindrome c₂ t₂))⁻¹ * (conjEval B)⁻¹ := by
          group

/-- **The adjacent case**, recovered from the general one at `B = []`.  This is
`GreendlingerRegime.mk_palindrome_mul_ne_one_of_minimal` with the leading block
`A` allowed to be nonempty, so it applies at every position of the expression
rather than only at its head. -/
theorem mk_palindrome_mul_ne_one_of_minimal_adjacent {R : Set (List (α × Bool))}
    {g : FreeGroup α} {A C : List (FreeGroup α × List (α × Bool))}
    {c₁ c₂ t₁ t₂ : List (α × Bool)}
    (hmin : IsMinimalConjExpr R
      (A ++ (FreeGroup.mk c₁, t₁) :: (FreeGroup.mk c₂, t₂) :: C) g) :
    FreeGroup.mk (palindrome c₁ t₁) * FreeGroup.mk (palindrome c₂ t₂) ≠ 1 := by
  intro hcan
  refine mk_palindrome_mul_ne_one_of_minimal_pair (A := A) (B := []) (C := C)
    (by simpa using hmin) ?_
  rw [conjEval_nil]
  simpa using hcan

end SmallCancellationRouter
end GroupApproximation
