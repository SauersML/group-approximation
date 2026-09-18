import GroupApproximation.Manuscript.NonMFSentences.IntroExamplesTorsionAllCharacteristics
import GroupApproximation.Manuscript.ChainCore.BilateralThreeZSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# Census bridges: three closed sentence endpoints

`non_mf_groups_exist.tex`.  Three printed sentences are closed by theorems in modules that the root
file did not import.  This file imports those modules and restates each theorem at the same type,
so that the census can point at root-reachable endpoints.

* tex 292–293 (census row `80279f06992b`), "Every example above has torsion, and in the lamp
  construction the obstruction is itself a torsion element".  The elementary examples are covered
  in every characteristic: the Weyl element `w = e₁₂(1) e₂₁(-1) e₁₂(1)` is a nontrivial torsion
  element of `EL_n(R)` for every nonzero ring `R` and every `n ≥ 2`.
  Endpoint: `printedIntroExamplesTorsionAllCharacteristics_closed`.
* `prop:bilateral-three`, tex 1583 (census row `cd7908a482b5`), "Hence $z\in\mathfrak D_B(L)$".
  Endpoint: `printedBilateralThreeZInDefect_closed`.
* `prop:bilateral-three`, tex 1587–1588 (census row `3550126258fb`),
  "Theorem~\ref{thm:compression-criterion} kills $z$ under every MF homomorphism from $B$, hence from
  $\GL_3(R_X)$".  Endpoint: `printedBilateralThreeCompressionKillsZ_closed`.
-/

namespace GroupApproximation.Full.NM14

/-- **tex 292–293**, with the elementary examples in every characteristic: the printed torsion sentence,
and a nontrivial element of finite order in `EL_n(R)` for every nonzero ring `R` and every `n ≥ 2`. -/
theorem printedIntroExamplesTorsionAllCharacteristics_closed :
    GroupApproximation.Manuscript.NonMFSentences.IntroExamplesTorsion.PrintedIntroExamplesTorsionAllCharacteristics :=
  GroupApproximation.Manuscript.NonMFSentences.IntroExamplesTorsion.printedIntroExamplesTorsionAllCharacteristics

/-- **`prop:bilateral-three`, tex 1583**, "Hence $z\in\mathfrak D_B(L)$": for every clopen `P` with
`T(P) ⊆ P` and every finite field, the central defect `z` of the cell lies in `B = ⟨L, W, c, y⟩`
and in the printed defect `𝔇_B(L)` of `L = EL_3(S)`. -/
theorem printedBilateralThreeZInDefect_closed :
    GroupApproximation.Manuscript.ChainCore.BilateralThree.PrintedBilateralThreeZInDefect :=
  GroupApproximation.Manuscript.ChainCore.BilateralThree.printedBilateralThreeZInDefect_closed

/-- **`prop:bilateral-three`, tex 1587–1588**: under the compression criterion, every homomorphism
from `B` to an MF group kills `z`, and so does every homomorphism from `GL_3(R_X)` to an MF group. -/
theorem printedBilateralThreeCompressionKillsZ_closed :
    GroupApproximation.Manuscript.ChainCore.BilateralThree.PrintedBilateralThreeCompressionKillsZ :=
  GroupApproximation.Manuscript.ChainCore.BilateralThree.printedBilateralThreeCompressionKillsZ_closed

end GroupApproximation.Full.NM14

#audit_closed_axioms GroupApproximation.Full.NM14.printedIntroExamplesTorsionAllCharacteristics_closed
#audit_closed_axioms GroupApproximation.Full.NM14.printedBilateralThreeZInDefect_closed
#audit_closed_axioms GroupApproximation.Full.NM14.printedBilateralThreeCompressionKillsZ_closed
