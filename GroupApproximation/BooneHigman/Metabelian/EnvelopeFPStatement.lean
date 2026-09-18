import GroupApproximation.BooneHigman.Metabelian.EnvelopeRN
import Mathlib.GroupTheory.FinitelyPresentedGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite presentation of Röver–Nekrashevych groups: the target statement

For a finite alphabet `X` with at least two letters and a finitely presented self-similar
group `H ≤ Aut(T_X)`, the Röver–Nekrashevych group `V_X(H)` (`roverNekrashevych X H`) is
finitely presented (Nekrashevych 2018 for contracting `H`; Skipper–Witzel–Zaremsky and
Zaremsky, arXiv:2405.09722, Section 3, for finitely presented self-similar `H`).

This is the finite-presentation conjunct of `RoverNekrashevychEnvelopeStatement`
(`EnvelopeReduction.lean`).  It is recorded here under the primed name
`RNFinitelyPresentedStatement'`, which is the form consumed by `EnvelopeFPSection.lean`
and `ChainWiredEnvelope.lean`.

*Truth.*  The special case `H = ⊥` (self-similar by `isSelfSimilar_bot`, finite hence finitely
presented) is Higman's theorem that `V_{d,1}` is finitely presented, `d = |X| ≥ 2`.  In
general `V_X(H)` is a quotient of `V_X ∗ H` by finitely many splitting and commutation relators
(Zaremsky, Section 3).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

/-- **Röver–Nekrashevych groups of finitely presented self-similar groups are finitely
presented.** -/
def RNFinitelyPresentedStatement' : Prop :=
  ∀ (X : Type) [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X)), IsSelfSimilar H →
    Group.IsFinitelyPresented ↥H → Group.IsFinitelyPresented ↥(roverNekrashevych X H)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNFinitelyPresentedStatement'

end GroupApproximation.BooneHigman.Metabelian.Envelope
