import GroupApproximation.Computability.FreeGroupCheckerPrimrec
import GroupApproximation.Computability.PresentationCodes

/-!
# Triviality of a coded word, decided on raw letters

`wordOf c w` lives in `FreeGroup (Fin (genCount c))`, a type that *depends on
the code*, and that dependence is the obstacle `AdianRabinWordProblem` records:
a search space has to be `Primcodable`, and a dependent family is not.  The
deletion checker of `FreeGroupCheckerPrimrec` works on `List (ℕ × Bool)`, which
is `Primcodable`, so what is needed is a bridge between the two.

The bridge is normalisation.  `letterOf c i` is `i % genCount c`, so distinct
raw letters collapse, and triviality of `wordOf c w` is *not* triviality of `w`
read in `FreeGroup ℕ`.  It becomes so once the letters are reduced:

* `map_val_wordOf` — pushing `wordOf c w` along `Fin.val` gives exactly
  `FreeGroup.mk (normLetters c w)`, because `Fin.val ∘ letterOf c` is `· % genCount c`.
* `wordOf_eq_one_iff` — and `Fin.val` is injective, so `FreeGroup.map` of it is
  injective (`FreeGroup.map_injective`), which lets triviality be reflected back.

Composing with `mk_eq_one_iff_exists_steps` gives
`wordOf_eq_one_iff_exists_steps`: the coded word dies in the *free* group
exactly when a deletion certificate exists for its normalised raw form — a
statement quantifying only over `List ℕ`, with no dependent type and no
free-group element in the search space.

That is the equality test the raw-certificate route needs; what it does not yet
do is the normal-closure half, where the certificate names conjugated relators.
-/

namespace GroupApproximation
namespace Computability

open PresentationCodes

/-- Raw letters reduced into the code's alphabet range. -/
def normLetters (c : PresentationCode) (w : List (ℕ × Bool)) : List (ℕ × Bool) :=
  w.map fun p => (p.1 % genCount c, p.2)

/-- Pushing a coded word along `Fin.val` is reading its normalised raw form in
`FreeGroup ℕ`. -/
theorem map_val_wordOf (c : PresentationCode) (w : List (ℕ × Bool)) :
    FreeGroup.map (Fin.val : Fin (genCount c) → ℕ) (wordOf c w)
      = FreeGroup.mk (normLetters c w) := by
  rw [wordOf, FreeGroup.map.mk, List.map_map]
  rfl

/-- **Triviality is decided on normalised raw letters.**  The dependent type is
gone from the right-hand side. -/
theorem wordOf_eq_one_iff (c : PresentationCode) (w : List (ℕ × Bool)) :
    wordOf c w = 1 ↔ FreeGroup.mk (normLetters c w) = 1 := by
  rw [← map_val_wordOf]
  constructor
  · intro h; rw [h, map_one]
  · intro h
    exact FreeGroup.map_injective Fin.val_injective (by rw [h, map_one])

/-- **The certificate form.**  A coded word dies in the free group exactly when
its normalised raw form admits a deletion certificate — quantifying over
`List ℕ` alone. -/
theorem wordOf_eq_one_iff_exists_steps (c : PresentationCode) (w : List (ℕ × Bool)) :
    wordOf c w = 1 ↔ ∃ is : List ℕ, applySteps (normLetters c w) is = some [] :=
  (wordOf_eq_one_iff c w).trans mk_eq_one_iff_exists_steps

/-- Normalisation is primitive recursive, so the bridge costs the search
nothing. -/
theorem primrec_normLetters : Primrec₂ normLetters := by
  have hgen : Primrec fun x : PresentationCode × List (ℕ × Bool) => genCount x.1 :=
    Primrec.succ.comp (Primrec.fst.comp Primrec.fst)
  refine Primrec.list_map (Primrec.snd) ?_
  exact (Primrec.pair
    (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd) (hgen.comp Primrec.fst))
    (Primrec.snd.comp Primrec.snd)).to₂

end Computability
end GroupApproximation
