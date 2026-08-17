import GroupApproximation.Computability.BooneWordMapPrimrec
import GroupApproximation.Computability.AdianRabinWordProblem

/-!
# The code reads the halting word as the halting element

`BooneWords` writes the halting word as raw data and proves the *presentation*
reads it correctly (`equiv_commElt`).  What a reduction needs is the statement
one level out: that the **code's** word problem on that raw word is the
triviality of the halting element.

The step between them is a renumbering.  `stageCode` relabels the stage's
relators along `P.enum`, so the code presents the relabelled presentation rather
than the presentation itself, and a word written in the code's numbering is the
relabelling of the corresponding word in the stage's letters.  Triviality moves
across that renumbering by `PresentedGroupRelabel.mk_relabel_eq_one_iff`, which
is exactly the lemma for the purpose: it transfers `= 1` without asking for the
elements to be identified.

That is why nothing here has to track a word through the four equivalences
composing `stageCodeEquiv`.  Only triviality is at stake, and triviality is the
one thing the renumbering lemma moves directly.
-/

namespace GroupApproximation
namespace Computability

open BooneWords PresentationCodes RawWord BooneGroup Base BooneBaseWords
open BooneTowerPresentation
open PresentedGroupRelabel AdianRabinWordProblem

variable {S : Stage} (P : StagePres S)

/-- The code reads the halting word as the relabelling of the halting word in
the stage's own letters.  Same shape as `wordOf_rawTw`, one layer up. -/
theorem wordOf_rawComm (q : ℕ × ℕ) :
    wordOf (stageCode (finalPres P)) (rawComm P q)
      = relabel ((finalPres P).enum : (finalPres P).Letters → Fin ((finalPres P).gpred + 1))
          ((FreeGroup.of (kLetter P))⁻¹ *
            (finalPres P).word (twWord ((q.1 : ℤ), (q.2 : ℤ))) *
            FreeGroup.of (kLetter P) *
            ((finalPres P).word (twWord ((q.1 : ℤ), (q.2 : ℤ))))⁻¹) := by
  show wordOf (stageCode (finalPres P))
      ((kIdx P, false) :: (rawTw (finalPres P) q ++
        (kIdx P, true) :: invWord (rawTw (finalPres P) q))) = _
  rw [wordOf_cons_neg, wordOf_append, wordOf_cons_pos, wordOf_invWord,
    wordOf_rawTw, letterOf_kIdx]
  simp only [map_mul, map_inv, FreeGroup.map.of, mul_assoc]
  rfl

end Computability
end GroupApproximation
