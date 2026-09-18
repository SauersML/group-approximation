import GroupApproximation.GGT.HullSCLemma51LetterPullbackHolds
import GroupApproximation.Meta.AxiomGuard

/-!
# The embedded Lemma 5.1 bridge, at every universe

Manuscript `non_mf_groups_exist.tex`, line 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}` (citing Hull, Theorem 7.1):
"Then there is a surjective homomorphism $\varphi\colon G\to Q$ such that $Q$ is acylindrically
hyperbolic, ...".

Hull's proof of Theorem 7.1 passes through Osin's Lemma 5.1 (a linear relative isoperimetric
inequality for the small cancellation quotient) and Dahmani--Guirardel--Osin's Theorem 4.24 (linear
relative area gives hyperbolic embeddedness of the image peripheral family).  In this corpus that
leaf is `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`
(`GGT/HullSCLemma51EmbeddedBridge.lean`): for a hyperbolically embedded source family, a strongly
bounded Lemma 4.4 input, a quotient whose kernel is the normal closure of the relators, and
certificates at least-area diagrams with a quasi-geodesic spelling, the image family
`D.mapSurjective q hq` is hyperbolically embedded.

This module proves that Prop with no hypotheses and at arbitrary universes `u, v, w` (the corpus
endpoint `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed` is the `{0, 0, 0}`
instance).

## Route

* Clause (a), hyperbolicity of the quotient relative Cayley graph:
  `HullSC.hyperbolic_mapSurjective_of_leastAreaCertificates` (`GGT/HullSCLemma51QuotientStokes`):
  four-point hyperbolicity of the source gives a linear Stokes inequality, the least-area
  certificates push it to the quotient alphabet, and Gromov's theorem (Bowditch's slim-triangle
  criterion) gives hyperbolicity.
* Clause (b), local finiteness of the quotient relative metrics:
  `HullSC.locallyFinite_mapSurjective_of_letterPullback` (`GGT/HullSCLemma51EmbeddedProducer`)
  from the letter pullback `HullSC.quotientPeripheralLetterPullbackStatement_holds`
  (`GGT/HullSCLemma51LetterPullbackHolds`): induction on the quotient ball radius, with one
  shortcut move for a word with a non-geodesic rotation and one certificate cut otherwise.
* The two clauses are assembled by
  `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback`.

Every producer on this route is universe-polymorphic and takes only the printed inputs of the
leaf; none takes a `...Statement` binder.
-/

namespace GroupApproximation.GGT.IsoperimetricBridgeLeaf

universe u v w

/-- **Osin's Lemma 5.1 bridge, embedded form, unconditionally.**  For every hyperbolically
embedded relative generating set `D`, every strongly bounded Lemma 4.4 family `W`, and every
surjection `q` with kernel the normal closure of `W` and certificates at least-area diagrams with a
quasi-geodesic spelling, the image family `D.mapSurjective q hq` is hyperbolically embedded. -/
theorem manuscriptSentence_relativeIsoperimetricBridgeQuasiGeodesicEmbedded :
    GroupApproximation.HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{u, v, w} :=
  GroupApproximation.HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback
    GroupApproximation.HullSC.quotientPeripheralLetterPullbackStatement_holds

end GroupApproximation.GGT.IsoperimetricBridgeLeaf

#audit_axioms GroupApproximation.GGT.IsoperimetricBridgeLeaf.manuscriptSentence_relativeIsoperimetricBridgeQuasiGeodesicEmbedded
#audit_closed_axioms GroupApproximation.GGT.IsoperimetricBridgeLeaf.manuscriptSentence_relativeIsoperimetricBridgeQuasiGeodesicEmbedded
