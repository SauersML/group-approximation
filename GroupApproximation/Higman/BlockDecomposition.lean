import GroupApproximation.Higman.CodedAbsorber

/-!
# Block decomposition of a raw word in the coded absorber

`Higman.CodedAbsorber` supplies the first two fields of a
`Higman.RecursivePresentation Higman.PCDirectSum`: the generating family
`pcGen` and `spans_pcGen`.  The third field is

    REPred (fun w : RawWord => evalRaw pcGen w = 1) ,

and this file reduces that, with no computability at all, to a **finite
conjunction whose index list is read off `w`**.

## The reduction

A generator `pcGen n` lives in one coordinate, the code `blockOf n`, and its
coordinate value is one generator of that coded group.  So for a fixed code
`c`, all the letters of `w` outside block `c` evaluate to `1` in coordinate
`c` and may be deleted (`evalRaw_filter`).  Triviality in the restricted
direct product is triviality in every coordinate
(`pcDirectSum_eq_one_iff`), so

    evalRaw pcGen w = 1  ↔  ∀ c, the block-`c` subword of `w` is trivial in
                              the coded group of `c`.

Finally a code that is not the block of any letter of `w` has empty subword,
so the quantifier may be restricted to `w.map (blockOf ∘ Prod.fst)`, a list
computed from `w` by a map --- `evalRaw_pcGen_eq_one_iff_blocks`.

## What is left of (B1) after this file

Two things, both computability:

* the per-block condition is the word problem of one finite presentation, so
  it has to be identified with `AdianRabinWordProblem.wordProblemPred` at the
  code `c` and the re-indexed subword.  That is an equation between two
  evaluations of the same raw word and needs `PresentationCodes.wordOf`;
* a finite conjunction of recursively enumerable conditions, over a list
  computed from the input, is recursively enumerable.  The economical route
  is not to close `REPred` under conjunction but to merge the certificates:
  `AdianRabinWordProblem.wordProblemPred_iff` presents each block's condition
  as one existential over a `Primcodable` certificate with a decidable
  matrix, so the conjunction is a single existential over a *list* of
  certificates, which is the shape `WordProblemRE.rePred_exists_eq_true`
  already consumes.

Neither is done here, and no declaration below pretends otherwise.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.Chiodo
open GroupApproximation.PresentationCodes

/-! ## 1.  Which block a generator lives in -/

/-- The code whose coordinate the `n`-th generator occupies. -/
def blockOf (n : ℕ) : PresentationCode := codeOfNat n.unpair.1

/-- Which generator of that code it is. -/
def letterIndex (n : ℕ) : ℕ := n.unpair.2

theorem pcGen_eq (n : ℕ) :
    pcGen n =
      pcOf (blockOf n)
        (PresentedGroup.of (letterOf (blockOf n) (letterIndex n))) :=
  rfl

/-- A coordinate inclusion is killed by every other coordinate's
evaluation. -/
theorem pcEval_pcOf_of_ne {c d : PresentationCode} (h : d ≠ c) (y : Carrier d) :
    pcEval c (pcOf d y) = 1 := by
  classical
  simp [pcOf, pcEval, DFinsupp.single_eq_of_ne h]

theorem pcEval_pcGen_self (n : ℕ) :
    pcEval (blockOf n) (pcGen n) =
      PresentedGroup.of (letterOf (blockOf n) (letterIndex n)) :=
  pcEval_pcOf _ _

theorem pcEval_pcGen_of_ne {c : PresentationCode} {n : ℕ} (h : blockOf n ≠ c) :
    pcEval c (pcGen n) = 1 :=
  pcEval_pcOf_of_ne h _

/-! ## 2.  Coordinatewise triviality -/

/-- An element of the restricted direct product is trivial exactly when every
coordinate of it is. -/
theorem pcDirectSum_eq_one_iff (g : PCDirectSum) :
    g = 1 ↔ ∀ c : PresentationCode, pcEval c g = 1 := by
  constructor
  · intro h c
    rw [h, map_one]
  · intro h
    apply Multiplicative.toAdd.injective
    apply DFinsupp.ext
    intro c
    apply Additive.toMul.injective
    simpa [pcEval] using h c

/-! ## 3.  Deleting the letters that do not matter -/

variable {A : Type} [Group A]

/-- **Letters whose generator is trivial may be deleted.**  The list-level
form of `evalRaw_eq_one_of_letters`, and the only combinatorial ingredient of
the block decomposition. -/
theorem evalRaw_filter (x : ℕ → A) (P : ℕ × Bool → Bool) (w : RawWord)
    (h : ∀ p ∈ w, P p = false → x p.1 = 1) :
    evalRaw x (w.filter P) = evalRaw x w := by
  induction w with
  | nil => simp
  | cons p w ih =>
      have ih' : evalRaw x (w.filter P) = evalRaw x w :=
        ih fun q hq hq' => h q (List.mem_cons_of_mem _ hq) hq'
      cases hP : P p with
      | true =>
          rw [List.filter_cons_of_pos hP]
          obtain ⟨i, b⟩ := p
          rw [evalRaw_cons, evalRaw_cons, ih']
      | false =>
          rw [List.filter_cons_of_neg (by simp [hP])]
          have hx : x p.1 = 1 := h p (by simp) hP
          obtain ⟨i, b⟩ := p
          rw [evalRaw_cons, ih']
          simp at hx
          cases b <;> simp [hx]

/-! ## 4.  The block decomposition -/

/-- **Triviality is block by block.** -/
theorem evalRaw_pcGen_eq_one_iff (w : RawWord) :
    evalRaw pcGen w = 1 ↔
      ∀ c : PresentationCode,
        evalRaw (fun n ↦ pcEval c (pcGen n))
          (w.filter fun p ↦ decide (blockOf p.1 = c)) = 1 := by
  rw [pcDirectSum_eq_one_iff]
  refine forall_congr' fun c => ?_
  have hfil : evalRaw (fun n ↦ pcEval c (pcGen n))
      (w.filter fun p ↦ decide (blockOf p.1 = c))
      = evalRaw (fun n ↦ pcEval c (pcGen n)) w := by
    refine evalRaw_filter _ _ w ?_
    intro p _ hp
    exact pcEval_pcGen_of_ne (by simpa using hp)
  rw [map_evalRaw, ← hfil]

/-- **Only the blocks occurring in `w` have to be checked**, and they are read
off `w` by a map.  This is the finite, computable conjunction that (B1)'s
remaining field is about. -/
theorem evalRaw_pcGen_eq_one_iff_blocks (w : RawWord) :
    evalRaw pcGen w = 1 ↔
      ∀ c ∈ w.map (fun p ↦ blockOf p.1),
        evalRaw (fun n ↦ pcEval c (pcGen n))
          (w.filter fun p ↦ decide (blockOf p.1 = c)) = 1 := by
  rw [evalRaw_pcGen_eq_one_iff]
  constructor
  · intro h c _
    exact h c
  · intro h c
    by_cases hc : c ∈ w.map (fun p ↦ blockOf p.1)
    · exact h c hc
    · refine evalRaw_eq_one_of_letters _ _ ?_
      intro p hp
      have hp' := List.mem_filter.1 hp
      exact absurd (List.mem_map.2 ⟨p, hp'.1, by simpa using hp'.2⟩) hc

/-! ## 5.  Re-indexing a single block

The block-`c` subword is indexed by *global* generator numbers; the coded
group of `c` is generated by its own letters.  This is the translation, and
it is the last purely algebraic step before the per-block condition can be
recognized as `AdianRabinWordProblem.wordProblemPred` at `c`. -/

theorem pcEval_pcGen_of_eq {c : PresentationCode} {n : ℕ} (h : blockOf n = c) :
    pcEval c (pcGen n) = PresentedGroup.of (letterOf c (letterIndex n)) := by
  subst h
  exact pcEval_pcGen_self n

/-- **The block-`c` subword, re-indexed by the letters of `c`.**  On a word
all of whose letters lie in block `c`, evaluating coordinate `c` of the
generators is the same as evaluating the coded group's own generators at the
letter indices. -/
theorem evalRaw_reindex (c : PresentationCode) (v : RawWord)
    (hv : ∀ p ∈ v, blockOf p.1 = c) :
    evalRaw (fun n ↦ pcEval c (pcGen n)) v
      = evalRaw (fun k ↦ (PresentedGroup.of (letterOf c k) : Carrier c))
          (v.map fun p ↦ (letterIndex p.1, p.2)) := by
  induction v with
  | nil => simp
  | cons p v ih =>
      have ih' := ih fun q hq => hv q (List.mem_cons_of_mem _ hq)
      have hp : blockOf p.1 = c := hv p (by simp)
      obtain ⟨i, b⟩ := p
      simp only [List.map_cons]
      rw [evalRaw_cons, evalRaw_cons, ih', pcEval_pcGen_of_eq hp]

/-- The block decomposition in the form the computability step consumes: a
finite conjunction, indexed by a list computed from `w`, of triviality
statements about the coded groups' own generators. -/
theorem evalRaw_pcGen_eq_one_iff_reindexed (w : RawWord) :
    evalRaw pcGen w = 1 ↔
      ∀ c ∈ w.map (fun p ↦ blockOf p.1),
        evalRaw (fun k ↦ (PresentedGroup.of (letterOf c k) : Carrier c))
          (((w.filter fun p ↦ decide (blockOf p.1 = c))).map
            fun p ↦ (letterIndex p.1, p.2)) = 1 := by
  rw [evalRaw_pcGen_eq_one_iff_blocks]
  refine forall_congr' fun c => ?_
  refine imp_congr_right fun _ => ?_
  rw [evalRaw_reindex c _ ?_]
  intro p hp
  simpa using (List.mem_filter.1 hp).2

end Higman
end GroupApproximation
