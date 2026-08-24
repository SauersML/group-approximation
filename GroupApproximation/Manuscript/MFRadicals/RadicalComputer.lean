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

/-- **Theorem D.**  One finitely presented non-MF group carrying a computable
family of MF-invisible words whose triviality problem is undecidable. -/
theorem manuscriptTheoremD :
    Group.IsFinitelyPresented MFRadicalComputer.Carrier ∧
      ¬ IsOperatorMF MFRadicalComputer.Carrier ∧
      (∀ p, NormMFInvisible (MFRadicalComputer.word p)) ∧
      (∀ p, MFRadicalComputer.word p = 1 ↔
        MFRadicalComputer.controlMachine.Halts p) ∧
      ¬ ComputablePred fun p : ℕ × ℕ => MFRadicalComputer.word p = 1 :=
  MFRadicalComputer.closed_package

end MFRadicals
end Manuscript
end GroupApproximation
