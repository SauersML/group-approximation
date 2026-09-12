import Mathlib.GroupTheory.CoprodI

/-!
# Inversion of reduced words in a free product

Mathlib's normal form for `Monoid.CoprodI` is head-oriented: `Word.fstIdx`
reads the first letter, `Word.equivPair` splits it off, and the `MulAction`
that drives the whole development multiplies on the left.  There is nothing
for the *last* letter.

That is the one gap that blocks cyclic reduction, and with it "a free product
of torsion-free groups is torsion-free"
(`Algebra.CoprodITorsionFree`): the cyclic-reduction induction conjugates by
the head letter so that it merges with the last one, and the merge is a
back-end operation.

The economical repair is not to build a back-end API but to invert: this file
gives `invWord`, the letterwise inverse reversed, proves it is again reduced,
that its product is the inverse (`prod_invWord`), and that it *is* the reduced
word of the inverse (`equiv_inv`).  Since inversion preserves length
(`length_invWord`), every statement about the last letter of `x` becomes a
statement about the first letter of `x⁻¹`, where Mathlib's API applies.

Reducedness of the reversed word is where the two hypotheses of `Word` are
checked: `ne_one` because a letter is nontrivial exactly when its inverse is,
and `chain_ne` because the relation "different summands" is symmetric, so it
survives `List.isChain_reverse` after `List.isChain_map`.
-/

namespace GroupApproximation
namespace CoprodIWordInverse

open Monoid Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

/-! ## 1.  The reversed letterwise inverse -/

/-- The letterwise inverse of a list of letters, reversed. -/
def invList (l : List (Σ i, G i)) : List (Σ i, G i) :=
  (l.map fun p ↦ (⟨p.1, p.2⁻¹⟩ : Σ i, G i)).reverse

@[simp] theorem invList_nil : invList ([] : List (Σ i, G i)) = [] := rfl

theorem invList_cons (p : Σ i, G i) (l : List (Σ i, G i)) :
    invList (p :: l) = invList l ++ [(⟨p.1, p.2⁻¹⟩ : Σ i, G i)] := by
  simp [invList]

theorem mem_invList {l : List (Σ i, G i)} {q : Σ i, G i} :
    q ∈ invList l ↔ ∃ p ∈ l, (⟨p.1, p.2⁻¹⟩ : Σ i, G i) = q := by
  simp [invList, List.mem_reverse, List.mem_map]

@[simp] theorem length_invList (l : List (Σ i, G i)) :
    (invList l).length = l.length := by
  simp [invList]

/-! ## 2.  It is again a reduced word -/

/-- The inverse of a reduced word. -/
def invWord (w : Word G) : Word G where
  toList := invList w.toList
  ne_one := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_invList.1 hq
    simpa using w.ne_one p hp
  chain_ne := by
    refine List.isChain_reverse.2 ?_
    refine (List.isChain_map _).2 ?_
    exact w.chain_ne.imp fun _ _ h => Ne.symm h

@[simp] theorem invWord_toList (w : Word G) :
    (invWord w).toList = invList w.toList := rfl

@[simp] theorem length_invWord (w : Word G) :
    (invWord w).toList.length = w.toList.length := by
  simp

/-! ## 3.  Its product is the inverse -/

theorem prod_invWord (w : Word G) : Word.prod (invWord w) = (Word.prod w)⁻¹ := by
  have key : ∀ l : List (Σ i, G i),
      List.prod ((invList l).map fun q ↦ (CoprodI.of q.snd : CoprodI G))
        = (List.prod (l.map fun q ↦ (CoprodI.of q.snd : CoprodI G)))⁻¹ := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
        rw [invList_cons, List.map_append, List.prod_append, ih]
        simp [mul_inv_rev]
  exact key w.toList

/-! ## 4.  It is the reduced word of the inverse -/

variable [DecidableEq ι] [∀ i, DecidableEq (G i)]

theorem equiv_inv (x : CoprodI G) :
    Word.equiv x⁻¹ = invWord (Word.equiv x) := by
  apply Word.equiv.symm.injective
  have h₁ : Word.equiv.symm (Word.equiv x⁻¹) = x⁻¹ := Word.equiv.symm_apply_apply _
  have h₂ : Word.equiv.symm (Word.equiv x) = x := Word.equiv.symm_apply_apply _
  have h₃ : Word.equiv.symm (invWord (Word.equiv x))
      = Word.prod (invWord (Word.equiv x)) := rfl
  rw [h₁, h₃, prod_invWord]
  show x⁻¹ = (Word.equiv.symm (Word.equiv x))⁻¹
  rw [h₂]

/-- **Inversion preserves the length of the reduced word.**  This is what
turns a statement about the last letter of `x` into one about the first letter
of `x⁻¹`. -/
@[simp] theorem length_equiv_inv (x : CoprodI G) :
    (Word.equiv x⁻¹).toList.length = (Word.equiv x).toList.length := by
  rw [equiv_inv, length_invWord]

/-- The last letter of `x`, read as the first letter of `x⁻¹`. -/
theorem fstIdx_inv (x : CoprodI G) :
    Word.fstIdx (Word.equiv x⁻¹)
      = ((Word.equiv x).toList.getLast?).map Sigma.fst := by
  rw [equiv_inv]
  show ((invList (Word.equiv x).toList).head?).map Sigma.fst = _
  rw [invList, List.head?_reverse, List.getLast?_map]
  cases h : (Word.equiv x).toList.getLast? with
  | none => simp
  | some p => simp

end CoprodIWordInverse
end GroupApproximation
