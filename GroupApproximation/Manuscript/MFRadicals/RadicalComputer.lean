import GroupApproximation.Computability.MFRadicalComputer

/-!
# Theorem D: the MF radical contains an undecidable computer

MF invisibility is not a synonym for "small central noise".  There is one fixed
finitely presented group `U` and a computable family of words `p ↦ r_p`, all of
them in the MF radical of `U`, for which deciding `r_p = 1` is undecidable.

So the word problem stays undecidable even when restricted to a promised
computable family lying entirely inside what MF approximation erases: the
invisible part can carry nonabelian derived structure and an undecidable
equality problem at the same time.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRadicals

/-- **Theorem D.**  There is *one* finitely presented non-MF group carrying a
computable family of words, every one of them invisible to MF approximation,
whose triviality problem is undecidable.

Stated as the paper displays it -- an existential over the group and the family
-- rather than as the concrete package of `Computability/MFRadicalComputer`,
which additionally names the controller and its halting problem. -/
theorem manuscriptTheoremD :
    ∃ (G : Type) (_ : Group G) (w : ℕ × ℕ → G),
      Group.IsFinitelyPresented G ∧ ¬ IsOperatorMF G ∧
        (∀ p, NormMFInvisible (w p)) ∧
        ¬ ComputablePred fun p : ℕ × ℕ => w p = 1 := by
  obtain ⟨hfp, hnot, hinv, -, hcomp⟩ := MFRadicalComputer.closed_package
  exact ⟨MFRadicalComputer.Carrier, inferInstance, MFRadicalComputer.word,
    hfp, hnot, hinv, hcomp⟩

end MFRadicals
end Manuscript
end GroupApproximation
