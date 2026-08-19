import GroupApproximation.Sofic.GreendlingerMirror

/-!
# Sliding a conjugator along its rotation, and the two shortening moves

`GreendlingerMinimal` spends minimality of the **factor count**: a shortest
expression has no two adjacent factors whose product is trivial.  That is the
whole of what the count buys, and it is not enough --- the two-factor descent
still asks that the destroyed block not swallow a rotation whole
(`TwoFactorRegime`).  What forbids *that* is minimality of the **total
conjugator length**, and this file builds the moves it is spent on.

## The freedom being exploited

A conjugate of a relator can be written with many different conjugators, because
the relator may be rotated: `c r c⁻¹ = (cz) (z⁻¹ r z) (cz)⁻¹`.  In palindromic
form this reads

* `mk (palindrome c (z ++ m)) = mk (palindrome (c ++ z) (m ++ z))` --- slide the
  conjugator *forward* past a prefix of the rotation, and
* `mk (palindrome c (m ++ z)) = mk (palindrome (c ++ invRev z) (z ++ m))` ---
  slide it *backward* past a suffix.

Both are one line of group algebra once `mk` is pushed through concatenation and
formal inversion; neither says anything about reduction, which is the point:
they are identities between the *elements*, and the weight of an expression is
measured by `FreeGroup.norm`, which only ever drops when a spelling is not
reduced.

## The two moves

The bad cases of the descent are the two ways the destroyed block can swallow a
rotation, and each has a move that strictly shortens the total conjugator
length.

* **Absorb** (`mk_palindrome_mul_absorb`).  If the other factor's rotation `t'`
  sits inside this factor's conjugator, `c = c' ++ (t' ++ q'')`, the two factors
  commute past each other and the copy of `t'` in the conjugator is deleted:
  the new conjugators are `c'` and `c' ++ q''`, a saving of `|t'|`.

* **Slide** (`mk_palindrome_mul_slide`).  If the block swallows `t` and leaves
  the two rotations overlapping in a piece `p` --- `c = c' ++ q`, `t' = q ++ p`,
  `invRev t = p ++ p'` --- the two factors swap and are re-conjugated to the
  meeting point `c' ++ invRev p`.  The new total is `2(|c'| + |p|)` against the
  old `2|c'| + |q|`, a saving of `|q| - 2|p|`, which `C'(1/6)` makes positive:
  `p` is a piece of `t'` and `q` is what is left of `t'` after it.

Both moves are stated as bare identities between products of palindromes, with
no hypotheses at all: the geometry that produces the decompositions lives in
`GreendlingerRegime`, and the weight bookkeeping in `GreendlingerWeight`.

Unconditional.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Pushing `mk` through the constructions -/

/-- `mk` turns concatenation into multiplication. -/
theorem mk_append_mul (X Y : List (α × Bool)) :
    FreeGroup.mk (X ++ Y) = FreeGroup.mk X * FreeGroup.mk Y :=
  FreeGroup.mul_mk.symm

/-- `mk` turns the formal inverse into inversion. -/
theorem mk_invRev_eq_inv (X : List (α × Bool)) :
    FreeGroup.mk (FreeGroup.invRev X) = (FreeGroup.mk X)⁻¹ :=
  FreeGroup.inv_mk.symm

/-- The reduced length of the element a word spells never exceeds the word. -/
theorem norm_mk_le_length [DecidableEq α] (X : List (α × Bool)) :
    FreeGroup.norm (FreeGroup.mk X) ≤ X.length :=
  FreeGroup.norm_mk_le

/-- For a reduced word the two agree. -/
theorem norm_mk_of_isReduced [DecidableEq α] {X : List (α × Bool)}
    (h : FreeGroup.IsReduced X) : FreeGroup.norm (FreeGroup.mk X) = X.length := by
  show (FreeGroup.mk X).toWord.length = X.length
  rw [FreeGroup.toWord_mk, h.reduce_eq]

/-! ## Sliding the conjugator -/

/-- **Sliding forward.**  A prefix of the rotation may be moved into the
conjugator, at the cost of rotating the relator by it. -/
theorem mk_palindrome_slide (c z m : List (α × Bool)) :
    FreeGroup.mk (palindrome c (z ++ m))
      = FreeGroup.mk (palindrome (c ++ z) (m ++ z)) := by
  simp only [mk_palindrome, mk_append_mul]
  group

/-- **Sliding backward.**  A suffix of the rotation may be moved into the
conjugator, inverted. -/
theorem mk_palindrome_slide_inv (c z m : List (α × Bool)) :
    FreeGroup.mk (palindrome c (m ++ z))
      = FreeGroup.mk (palindrome (c ++ FreeGroup.invRev z) (z ++ m)) := by
  simp only [mk_palindrome, mk_append_mul, mk_invRev_eq_inv]
  group

/-! ## Rotation by a prefix -/

/-- Rotating a concatenation by the length of its first block swaps the two
blocks. -/
theorem rotate_append {β : Type*} (X Y : List β) :
    (X ++ Y).rotate X.length = Y ++ X := by
  have hle : X.length ≤ (X ++ Y).length := by
    rw [List.length_append]
    omega
  rw [List.rotate_eq_drop_append_take hle, List.drop_left, List.take_left]

/-- Swapping the two blocks of a symmetrized relator gives a symmetrized
relator: the swap is a rotation. -/
theorem append_swap_mem_symmetrization {R : Set (List (α × Bool))}
    {X Y : List (α × Bool)} (h : X ++ Y ∈ symmetrization R) :
    Y ++ X ∈ symmetrization R := by
  have hrot := rotate_mem_symmetrization h X.length
  rwa [rotate_append] at hrot

/-! ## The two shortening moves -/

/-- **The absorb move.**  A factor whose conjugator begins with the *other*
factor's conjugator followed by that factor's whole rotation lets the two
factors be reordered, deleting the copy of the rotation from the conjugator.

The new conjugators are `c'` and `c' ++ q''`, against the old `c'` and
`c' ++ (t' ++ q'')`: a saving of `|t'|`, which is positive because relators are
nonempty. -/
theorem mk_palindrome_mul_absorb (c' t' q'' t : List (α × Bool)) :
    FreeGroup.mk (palindrome (c' ++ (t' ++ q'')) t)
        * FreeGroup.mk (palindrome c' t')
      = FreeGroup.mk (palindrome c' t')
        * FreeGroup.mk (palindrome (c' ++ q'') t) := by
  simp only [mk_palindrome, mk_append_mul]
  group

/-- **The slide move.**  When the cancellation swallows the first rotation and
the two rotations meet in `p` --- so that the first conjugator overhangs the
second by `q`, the second rotation is `q ++ p`, and the first inverted rotation
is `p ++ p'` --- the two factors swap and are both re-conjugated to the meeting
point `c' ++ invRev p`.

Old total conjugator length `2|c'| + |q|`; new total at most `2(|c'| + |p|)`.
The saving is `|q| - 2|p|`, positive under `C'(1/6)` because `p` is a piece of
the rotation `q ++ p`. -/
theorem mk_palindrome_mul_slide (c' q p p' : List (α × Bool)) :
    FreeGroup.mk (palindrome (c' ++ q)
          (FreeGroup.invRev p' ++ FreeGroup.invRev p))
        * FreeGroup.mk (palindrome c' (q ++ p))
      = FreeGroup.mk (palindrome (c' ++ FreeGroup.invRev p) (p ++ q))
        * FreeGroup.mk (palindrome (c' ++ FreeGroup.invRev p)
            (FreeGroup.invRev p' ++ FreeGroup.invRev p)) := by
  simp only [mk_palindrome, mk_append_mul, mk_invRev_eq_inv]
  group

/-- **The absorb move, mirrored.**  A *second* conjugator that begins with the
first conjugator followed by the first factor's inverted rotation: reordering
deletes that copy and saves `|t|`. -/
theorem mk_palindrome_mul_absorb_inv (c t Z t' : List (α × Bool)) :
    FreeGroup.mk (palindrome c t)
        * FreeGroup.mk (palindrome (c ++ (FreeGroup.invRev t ++ Z)) t')
      = FreeGroup.mk (palindrome (c ++ Z) t')
        * FreeGroup.mk (palindrome c t) := by
  simp only [mk_palindrome, mk_append_mul, mk_invRev_eq_inv]
  group

/-- **The meet move.**  When the second conjugator overhangs the first by `y`,
and `y` is what the first inverted rotation begins with --- `invRev t = y ++ v`,
`t' = v ++ u` --- the two factors swap and the second is re-conjugated to the
meeting point `c ++ invRev v`.

Old total conjugator length `2|c| + |y|`; new at most `2|c| + |v|`.  The saving
is `|y| - |v|`, positive under `C'(1/6)` because `v` is a piece of the rotation
`v ++ y`. -/
theorem mk_palindrome_mul_meet (c y v u : List (α × Bool)) :
    FreeGroup.mk (palindrome c (FreeGroup.invRev v ++ FreeGroup.invRev y))
        * FreeGroup.mk (palindrome (c ++ y) (v ++ u))
      = FreeGroup.mk (palindrome (c ++ FreeGroup.invRev v) (v ++ u))
        * FreeGroup.mk (palindrome c
            (FreeGroup.invRev v ++ FreeGroup.invRev y)) := by
  simp only [mk_palindrome, mk_append_mul, mk_invRev_eq_inv]
  group

end SmallCancellationRouter
end GroupApproximation
