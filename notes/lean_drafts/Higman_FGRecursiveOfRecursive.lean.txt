import GroupApproximation.Higman.EmbeddingTheorem
import GroupApproximation.Higman.RelatorSearch
import GroupApproximation.Higman.BlockWordProblem
import GroupApproximation.Computability.MarkovReductionInterface

/-!
# From a countably generated recursive presentation to a finite-rank one

The lane has two records for "recursively presented", and every closure tool
produces the wrong one for the bridge.

* `Higman.RecursivePresentation` (`Program.lean:207`) is countably generated:
  `gen : ℕ → A`, and the word problem is `REPred` over `RawWord`.  Every
  construction in `Higman.RelatorRE`, `RelatorEnumeration`,
  `RelabelPresentation` and `QuotientPresentation` produces this one.
* `Higman.FGRecursive` (`EmbeddingTheorem.lean:48`) is finite rank:
  `π : FreeGroup (Fin (rank+1)) →* A`, and the word problem is `REPred` over
  raw words read through `rawToFree`.  This is what `BridgeRecursive` and
  `ChiodoReduction` consume.

Nothing converted between them, which is why a proof of the bridge's
effectivity clause could not land even with the relator bookkeeping finished.
This file supplies the conversion.

## The shape of the hypothesis

Finite rank is genuinely extra data, so it has to be supplied: a finite
generating family and, crucially, a way to *rewrite* a word in the finite
alphabet as a word in the countable one.  That rewriting is what carries the
enumerability across, through `MarkovMFConsequences.rePred_comp`.

Two forms are given.

`fgRecursive_of_substitution` takes the rewriting as an opaque primitive
recursive map `subst : RawWord → RawWord` together with the identity it must
satisfy.  It is unconditional and is the form the bridge uses, because there
the rewriting is built by hand out of the generators' words.

`fgRecursive_of_wordFamily` is the convenience form: give a word `word k` for
each countable-alphabet letter and the letter-wise substitution is assembled
here.  Both forms are complete; the keystone does not depend on the
letter-wise one.

## Why substitution is stated over `RawWord` and not over free groups

House convention, and the reason is mechanical: `RawWord = List (ℕ × Bool)` is
`Primcodable` by `inferInstance`, while a dependent free-group type is not a
search space at all.  Everything primitive recursive in this development is a
list computation; the group-theoretic content enters only through `evalRaw`.
-/

namespace GroupApproximation
namespace Higman

/-! ## 1.  Substituting words for letters -/

/-- Substitute a word for each letter of a raw word, respecting signs. -/
def substRaw (word : ℕ → RawWord) : RawWord → RawWord
  | [] => []
  | (k, b) :: w => (if b then word k else invRaw (word k)) ++ substRaw word w

@[simp] theorem substRaw_nil (word : ℕ → RawWord) :
    substRaw word [] = [] := rfl

@[simp] theorem substRaw_cons (word : ℕ → RawWord) (k : ℕ) (b : Bool)
    (w : RawWord) :
    substRaw word ((k, b) :: w)
      = (if b then word k else invRaw (word k)) ++ substRaw word w := rfl

/-- **Substitution computes the reinterpreted value.**  Evaluating a
substituted word is evaluating the original word under the assignment that
sends each letter to the value of its replacement. -/
theorem evalRaw_substRaw {A : Type} [Group A] (x : ℕ → A)
    (word : ℕ → RawWord) (v : RawWord) :
    evalRaw x (substRaw word v)
      = evalRaw (fun k ↦ evalRaw x (word k)) v := by
  induction v with
  | nil => simp
  | cons p v ih =>
      obtain ⟨k, b⟩ := p
      rw [substRaw_cons, evalRaw_append, ih, evalRaw_cons]
      cases b
      · simp [evalRaw_invRaw]
      · simp

/-- Substitution as a flattened map, the form the primitive-recursive proof
wants.  Stated with `cond` rather than `if` because `Primrec.cond` is the
combinator that applies. -/
theorem substRaw_eq_flatten (word : ℕ → RawWord) (v : RawWord) :
    substRaw word v
      = (v.map fun p ↦ bif p.2 then word p.1 else invRaw (word p.1)).flatten := by
  induction v with
  | nil => rfl
  | cons p v ih =>
      obtain ⟨k, b⟩ := p
      cases b
      · show invRaw (word k) ++ substRaw word v = _
        rw [ih, List.map_cons, List.flatten_cons]
        rfl
      · show word k ++ substRaw word v = _
        rw [ih, List.map_cons, List.flatten_cons]
        rfl

/-! ## 2.  Reading a raw word at finite rank -/

/-- The letter of the finite alphabet a countable-alphabet index selects.
Indices are read modulo the alphabet size, matching `rawToFree` and
`Computability.PresentationCodes.wordOf`. -/
def finIdx (n : ℕ) (k : ℕ) : Fin (n + 1) :=
  ⟨k % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- A finite generating family, read as a countable one. -/
def finGen {A : Type} [Group A] (n : ℕ) (fgen : Fin (n + 1) → A) : ℕ → A :=
  fun k ↦ fgen (finIdx n k)

theorem rawToFree_eq_evalRaw (n : ℕ) (v : RawWord) :
    rawToFree n v = evalRaw (fun k ↦ FreeGroup.of (finIdx n k)) v := by
  rw [evalRaw_freeGroup]
  rfl

/-- **The presentation map at finite rank is `evalRaw` at the read-off
family.**  This is the bridge between the two records' word problems. -/
theorem lift_rawToFree {A : Type} [Group A] (n : ℕ) (fgen : Fin (n + 1) → A)
    (v : RawWord) :
    FreeGroup.lift fgen (rawToFree n v) = evalRaw (finGen n fgen) v := by
  rw [rawToFree_eq_evalRaw, map_evalRaw]
  simp only [FreeGroup.lift_apply_of]
  rfl

/-! ## 3.  The conversion -/

/-- **The keystone: a recursive presentation plus a primitive recursive
rewriting is a finite-rank recursive presentation.**

The rewriting `subst` turns a word in the finite alphabet into a word in the
countable one representing the same element; `rePred_comp` then pulls the
countable word problem back along it.  No hypothesis beyond that: the finite
family need not be related to `P.gen` in any other way. -/
def fgRecursive_of_substitution {A : Type} [Group A]
    (P : RecursivePresentation A) (n : ℕ) (fgen : Fin (n + 1) → A)
    (hsurj : Function.Surjective (FreeGroup.lift fgen))
    (subst : RawWord → RawWord) (hsubst : Primrec subst)
    (hcompat : ∀ v : RawWord,
      evalRaw P.gen (subst v) = evalRaw (finGen n fgen) v) :
    FGRecursive A where
  rank := n
  π := FreeGroup.lift fgen
  π_surjective := hsurj
  re := by
    have hpull : REPred fun v : RawWord ↦ evalRaw P.gen (subst v) = 1 :=
      MarkovMFConsequences.rePred_comp P.re hsubst.to_comp
    have hiff : (fun v : RawWord ↦ evalRaw P.gen (subst v) = 1)
        = fun v : RawWord ↦ FreeGroup.lift fgen (rawToFree n v) = 1 := by
      funext v
      rw [hcompat v, lift_rawToFree]
    rwa [hiff] at hpull

/-- **A letter-wise substitution is primitive recursive.**  Via
`substRaw_eq_flatten`: a `Primrec.list_map` of the sign-dispatch followed by
`Primrec.list_flatten`, in the same style as `Higman.primrec_invRaw`, which
rewrites `invRaw` into a `map`/`reverse` composite before proving it. -/
theorem primrec_substRaw {word : ℕ → RawWord} (hword : Primrec word) :
    Primrec (substRaw word) := by
  have hw : Primrec fun p : RawWord × (ℕ × Bool) ↦ word p.2.1 :=
    hword.comp (Primrec.fst.comp Primrec.snd)
  have hletter : Primrec₂ fun (_ : RawWord) (p : ℕ × Bool) ↦
      (bif p.2 then word p.1 else invRaw (word p.1)) :=
    (Primrec.cond (Primrec.snd.comp Primrec.snd) hw
      (primrec_invRaw.comp hw)).to₂
  have h : Primrec fun v : RawWord ↦
      (v.map fun p ↦ bif p.2 then word p.1 else invRaw (word p.1)).flatten :=
    Primrec.list_flatten.comp (Primrec.list_map Primrec.id hletter)
  exact h.of_eq fun v ↦ (substRaw_eq_flatten word v).symm

/-- **Convenience form: a word for each countable-alphabet letter.**  The
letter-wise substitution is assembled here, so a caller supplies only the
words and the identity they satisfy. -/
def fgRecursive_of_wordFamily {A : Type} [Group A]
    (P : RecursivePresentation A) (n : ℕ) (fgen : Fin (n + 1) → A)
    (hsurj : Function.Surjective (FreeGroup.lift fgen))
    (word : ℕ → RawWord) (hword : Primrec word)
    (hcompat : ∀ k : ℕ, evalRaw P.gen (word k) = finGen n fgen k) :
    FGRecursive A :=
  fgRecursive_of_substitution P n fgen hsurj (substRaw word)
    (primrec_substRaw hword)
    (fun v ↦ by
      rw [evalRaw_substRaw]
      exact congrArg (fun x : ℕ → A ↦ evalRaw x v) (funext hcompat))

end Higman
end GroupApproximation
