import GroupApproximation.Higman.RelatorWordProblem
import GroupApproximation.Higman.TowerDerivation

/-!
# The relator word problem as one search

`Higman.RelatorWordProblem` says a raw word dies in a presented group exactly
when its free value is a product of conjugates of relators.  This file puts
that in search form: the conjugation data becomes a list of raw words, and the
free-group equation becomes a *deletion certificate*, so the only remaining
non-decidable ingredient is membership in the relator set.

The deletion certificate is the repository's own device:
`Computability.mk_eq_one_iff_exists_steps` says a raw word is trivial in the
free group exactly when a list of cancellation positions reduces it to the
empty word, and `Computability.primrec_applySteps` says checking such a list is
primitive recursive.  Nothing here quantifies over free-group elements.

The shape reached is

    evalRaw gen w = 1  ↔  ∃ l, (every relator of `l` is in `S`)
                              ∧ ∃ steps, the word `conjWord₂ l ++ invRaw w`
                                          reduces to nothing,

which is one existential over `Primcodable` data as soon as membership in `S`
is itself presented that way --- and then
`WordProblemRE.rePred_exists_eq_true` applies, exactly as it did for
`Higman.BlockSearch` and `Higman.TowerCert`.
-/

namespace GroupApproximation
namespace Higman

variable {A : Type} [Group A]

/-! ## 1.  The conjugate product as a raw word -/

/-- The raw word spelling a product of conjugates, for (conjugator, base)
pairs.  The three-component version used by the tower is
`Higman.conjWord`. -/
def conjWord₂ (l : List (RawWord × RawWord)) : RawWord :=
  (l.map fun p ↦ p.1 ++ p.2 ++ invRaw p.1).flatten

theorem evalRaw_conjWord₂ (gen : ℕ → A) (l : List (RawWord × RawWord)) :
    evalRaw gen (conjWord₂ l)
      = conjProd (l.map fun p ↦ (evalRaw gen p.1, evalRaw gen p.2)) := by
  induction l with
  | nil => simp [conjWord₂]
  | cons p l ih =>
      show evalRaw gen ((p.1 ++ p.2 ++ invRaw p.1) ++ conjWord₂ l) = _
      rw [evalRaw_append, evalRaw_append, evalRaw_append, evalRaw_invRaw, ih]
      simp [conjProd_cons, mul_assoc]

/-! ## 2.  The free-group equation as a deletion certificate -/

theorem freeEval_eq_one_iff (v : RawWord) :
    freeEval v = 1 ↔ ∃ is : List ℕ, Computability.applySteps v is = some [] := by
  rw [freeEval_eq]
  have hmap : (v.map fun p ↦ (p.1, p.2)) = v := by
    induction v with
    | nil => rfl
    | cons p v ih =>
        rw [List.map_cons, ih, Prod.eta]
  rw [hmap]
  exact Computability.mk_eq_one_iff_exists_steps

/-! ## 3.  The search form -/

/-- **The word problem of a presented group, as one search.**

The right-hand side quantifies over raw words and lists of naturals only.  Its
matrix is decidable apart from the relator memberships, and those are the only
place the presentation's recursive enumerability is used. -/
theorem evalRaw_eq_one_iff_search (gen : ℕ → A) (S : Set (FreeGroup ℕ))
    (hpres : ∀ w : RawWord,
      evalRaw gen w = 1 ↔ freeEval w ∈ Subgroup.normalClosure S)
    (w : RawWord) :
    evalRaw gen w = 1 ↔
      ∃ l : List (RawWord × RawWord),
        (∀ p ∈ l, freeEval p.2 ∈ symmetrize S) ∧
          ∃ is : List ℕ,
            Computability.applySteps (conjWord₂ l ++ invRaw w) is = some [] := by
  rw [evalRaw_eq_one_iff_raw gen S hpres w]
  refine exists_congr fun l => and_congr_right fun _ => ?_
  rw [← freeEval_eq_one_iff]
  show _ ↔ freeEval (conjWord₂ l ++ invRaw w) = 1
  unfold freeEval
  rw [evalRaw_append, evalRaw_invRaw, evalRaw_conjWord₂, mul_inv_eq_one]

end Higman
end GroupApproximation
