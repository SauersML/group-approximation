import GroupApproximation.Algebra.CoprodICyclicReduction

/-!
# Alternating reduced words in a two-factor free product

The freeness argument for the Higman--Neumann--Neumann family expands a product
of `uₖ`'s into a word alternating between the two free generators, and then has
to say "that word is reduced, hence nontrivial".  Saying it needs a *witness*:
a `Word`, i.e. a list together with `ne_one` and `chain_ne`.

Assembling such a witness out of `NeWord.singleton` and `NeWord.append` is
awkward, because the constructors carry the end indices in their types.  For a
two-factor product the indices simply alternate, so the list can be written
down directly and both side conditions become transparent: `chain_ne` holds
because `s ≠ s + 1` in `Fin 2`, and `ne_one` because every entry's letter comes
from the given list.

`prod_altWord_ne_one` is the payoff, and with
`Algebra.CoprodICyclicReduction.prod_ne_one_of_toList_ne_nil` it needs no
`NeWord` at all.

Note that this stays in `FreeGroup Unit` rather than `Multiplicative ℤ`:
Mathlib's `freeGroupEquivCoprodI` carries an explicit warning that phrasing the
factors as `Multiplicative ℤ` runs into instance diamonds, and there is no need
to.
-/

namespace GroupApproximation
namespace CoprodIAltWord

open Monoid Monoid.CoprodI

variable {M : Fin 2 → Type*} [∀ i, Group (M i)]
variable {A : Type*}
variable {ι' : Type*}

/-- The letters of an alternating word, starting at index `s`. -/
def altList : Fin 2 → List A → List (Σ _ : Fin 2, A)
  | _, [] => []
  | s, a :: l => ⟨s, a⟩ :: altList (s + 1) l

theorem succ_ne_self (s : Fin 2) : s ≠ s + 1 := by
  omega

theorem mem_altList_snd :
    ∀ (s : Fin 2) (l : List A) (q : Σ _ : Fin 2, A),
      q ∈ altList s l → q.2 ∈ l := by
  intro s l
  induction l generalizing s with
  | nil => intro q hq; simp [altList] at hq
  | cons p l ih =>
      intro q hq
      rw [altList, List.mem_cons] at hq
      rcases hq with rfl | hq'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (s + 1) q hq')

theorem altList_chain :
    ∀ (s : Fin 2) (l : List A),
      (altList s l).IsChain fun p q ↦ p.1 ≠ q.1 := by
  intro s l
  induction l generalizing s with
  | nil => exact List.isChain_nil
  | cons p l ih =>
      cases l with
      | nil => exact List.IsChain.singleton _
      | cons p' l' =>
          rw [altList, altList, List.isChain_cons_cons]
          refine ⟨succ_ne_self s, ?_⟩
          have := ih (s + 1)
          rwa [altList] at this

/-- An alternating list of nontrivial letters, as a reduced word. -/
def altWord [Group A] (s : Fin 2) (l : List A) (hl : ∀ a ∈ l, a ≠ 1) :
    Word (fun _ : Fin 2 ↦ A) where
  toList := altList s l
  ne_one := by
    intro q hq
    exact hl q.2 (mem_altList_snd s l q hq)
  chain_ne := altList_chain s l

@[simp] theorem altWord_toList [Group A] (s : Fin 2) (l : List A)
    (hl : ∀ a ∈ l, a ≠ 1) : (altWord s l hl).toList = altList s l := rfl

theorem altList_ne_nil {s : Fin 2} {l : List A} (hl : l ≠ []) :
    altList s l ≠ [] := by
  cases l with
  | nil => exact absurd rfl hl
  | cons p l => simp [altList]

/-- **A nonempty alternating product of nontrivial letters is nontrivial.** -/
theorem prod_altWord_ne_one [Group A] [DecidableEq A]
    (s : Fin 2) (l : List A) (hl : ∀ a ∈ l, a ≠ 1) (hne : l ≠ []) :
    Word.prod (altWord s l hl) ≠ 1 :=
  CoprodICyclicReduction.prod_ne_one_of_toList_ne_nil
    (by rw [altWord_toList]; exact altList_ne_nil hne)

/-! ## The product of a letter list, without the side conditions

`Word.prod` needs a `Word`, and a `Word` carries its `ne_one` and `chain_ne`
proofs, which makes it a poor thing to compute with: any equation between two
words drags the proof terms along.  `listProd` is the same product taken on the
bare list, so the computation can be done first and the word assembled only at
the end, where nontriviality is actually needed. -/

/-- The product of a list of letters. -/
def listProd (l : List (Σ i, M i)) : CoprodI M :=
  (l.map fun p ↦ CoprodI.of p.2).prod

@[simp] theorem listProd_nil : listProd ([] : List (Σ i, M i)) = 1 := rfl

@[simp] theorem listProd_cons (p : Σ i, M i) (l : List (Σ i, M i)) :
    listProd (p :: l) = CoprodI.of p.2 * listProd l := by
  simp [listProd]

theorem word_prod_eq_listProd (w : Word M) : Word.prod w = listProd w.toList := rfl

/-- Two steps of an alternating list return to the starting index. -/
theorem altList_cons_cons (s : Fin 2) (a b : A) (l : List A) :
    altList s (a :: b :: l)
      = (⟨s, a⟩ : Σ _ : Fin 2, A) :: (⟨s + 1, b⟩ : Σ _ : Fin 2, A) :: altList s l := by
  show _ = _
  rw [altList, altList]
  congr 2
  have hperiod : s + 1 + 1 = s := by omega
  rw [hperiod]

theorem listProd_altList_cons_cons [Group A] (s : Fin 2) (a b : A) (l : List A) :
    listProd (altList s (a :: b :: l))
      = CoprodI.of (i := s) a * CoprodI.of (i := s + 1) b
          * listProd (altList s l) := by
  rw [altList_cons_cons, listProd_cons, listProd_cons, mul_assoc]

theorem listProd_altList_singleton [Group A] (s : Fin 2) (a : A) :
    listProd (altList s [a]) = CoprodI.of (i := s) a := by
  simp [altList]

/-! ## The general criterion

`altList` assigns indices automatically, which is convenient when the word
alternates between exactly two factors.  The expansion of the *second* family
of the Higman--Neumann--Neumann bridge, `gen k · uₖ`, runs over three factors
in the pattern `0,1,2,1,0,1,2,1,…`, so the indices have to be supplied by the
caller.  For that the general criterion is both simpler and stronger: a `Word`
is just a list with its two side conditions, so exhibiting them directly is
all that is needed.

`altWord` and `prod_altWord_ne_one` remain the convenient special case. -/

/-- **The general nontriviality criterion.**  A nonempty list of nontrivial
letters with consecutive indices distinct has nontrivial product. -/
theorem listProd_ne_one [DecidableEq ι'] {N : ι' → Type*} [∀ i, Group (N i)]
    [∀ i, DecidableEq (N i)]
    {l : List (Σ i, N i)} (hne : l ≠ [])
    (h1 : ∀ p ∈ l, p.2 ≠ 1)
    (h2 : l.IsChain fun p q ↦ p.1 ≠ q.1) :
    (l.map fun p ↦ CoprodI.of p.2).prod ≠ 1 := by
  have hw : Word.prod (⟨l, h1, h2⟩ : Word N) ≠ 1 :=
    CoprodICyclicReduction.prod_ne_one_of_toList_ne_nil hne
  exact hw

end CoprodIAltWord
end GroupApproximation
