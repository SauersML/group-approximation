import GroupApproximation.GGT.HullSCLemma51LetterPullbackHolds

/-!
# The embedded Lemma 5.1 bridge, closed

Manuscript line 1636, `\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`:
"Then there is a surjective homomorphism $\varphi\colon G\to Q$ such that $Q$ is acylindrically
hyperbolic".  The embedded Lemma 5.1 bridge gives the quotient its hyperbolically embedded
peripheral structure: a hyperbolic quotient Cayley graph (clause (a)) and locally finite relative
balls (clause (b)).  Clause (b) comes from the quotient peripheral letter pullback
(`quotientPeripheralLetterPullbackStatement_holds`).
-/

namespace GroupApproximation
namespace HullSC

/-- **The embedded Lemma 5.1 bridge**, for Hull's small cancellation theorem (manuscript line
1636, `\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`: "there is a surjective
homomorphism $\varphi\colon G\to Q$ such that $Q$ is acylindrically hyperbolic"). -/
theorem relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed :
    RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0} :=
  relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback
    quotientPeripheralLetterPullbackStatement_holds

end HullSC
end GroupApproximation

#audit_closed_axioms GroupApproximation.HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
