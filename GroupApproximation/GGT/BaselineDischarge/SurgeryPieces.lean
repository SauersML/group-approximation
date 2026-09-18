import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SectionResiduals
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SeparatingRemoval
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ChainRespell
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PendantRemoval
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CornerInsertion
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingChains
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94QuasiGeodesicRespell
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SeparatedInsertionProof
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CaseTwo
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOneRun
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CaseOneWalkHolds
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# Closed forms of the Lemma 9.4 surgery pieces

Osin (math/0411039v3, Appendix), Lemma 9.4, Case 2: "This contradicts our assumption that
`∑ l(t_i)` is minimal."  Several producers of the planar surgery of that proof take a piece as a
hypothesis, although every piece they take is already proved.  This file supplies those pieces
and states the results with no hypothesis beyond the configuration.

Route.

* `separatingPathRemovalInput_closed`: `separatingPathRemovalInput_of_pendant` applied to the
  closed `pendantPathRemovalInput`.
* `chainRespellInput_closed`: `chainRespellInput_of_pieces` applied to the closed
  `cornerInsertionInput` and to `separatingPathRemovalInput_closed`.
* `osinLemma94CuttingChainsInput_closed`: `osinLemma94CuttingChainsInput_of_pieces` applied to
  `chainRespellInput_closed`, `pendantPathRemovalInput` and `quasiGeodesicRespellInput`.
* `not_leaf_of_dartMinimal_closed`, `alpha_not_mem_of_dartMinimal_closed`: the two chain lemmas
  with `pendantPathRemovalInput` supplied.
* `osinLemma94CaseTwo_false_closed`: one backwards connector pair of Case 2, with the closed
  `separatedCornerInsertionInput` supplied.
* `osinLemma94CaseOneInput_closed`: Case 1, `osinLemma94CaseOneInput_of_walk` applied to the
  closed face walk `osinLemma94CaseOneWalk` and the closed same-kind pairs
  `osinLemma94CaseOneSameCell`.

## Manuscript status
Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 4.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.BaselineDischarge

universe u w v

open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- **Removing a path between two `G`-faces.**  The removal of a separating path, from the
closed removal of a pendant path. -/
theorem separatingPathRemovalInput_closed :
    GloballyDistinguishedSectionFamily.SeparatingPathRemovalInput.{u, w, v} :=
  GloballyDistinguishedSectionFamily.separatingPathRemovalInput_of_pendant
    GloballyDistinguishedSectionFamily.pendantPathRemovalInput

#audit_closed_axioms GroupApproximation.GGT.BaselineDischarge.separatingPathRemovalInput_closed

/-- **The respelling of a cutting chain.**  The closed corner insertion followed by the closed
removal of the transported chain. -/
theorem chainRespellInput_closed :
    GloballyDistinguishedSectionFamily.ChainRespellInput.{u, w, v} :=
  GloballyDistinguishedSectionFamily.chainRespellInput_of_pieces
    GloballyDistinguishedSectionFamily.cornerInsertionInput separatingPathRemovalInput_closed

#audit_closed_axioms GroupApproximation.GGT.BaselineDischarge.chainRespellInput_closed

/-- **The cutting chains are quasi-geodesic.**  "This contradicts our assumption that `∑ l(t_i)`
is minimal."  With the fewest darts, every cutting chain is `(λ, c + 2)`-quasi-geodesic. -/
theorem osinLemma94CuttingChainsInput_closed : OsinLemma94CuttingChainsInput.{u, w, v} :=
  osinLemma94CuttingChainsInput_of_pieces chainRespellInput_closed
    GloballyDistinguishedSectionFamily.pendantPathRemovalInput quasiGeodesicRespellInput

#audit_closed_axioms GroupApproximation.GGT.BaselineDischarge.osinLemma94CuttingChainsInput_closed

/-- **Case 1 of Lemma 9.4.**  "Case 1 … This contradicts the maximality of `M`."  The face walk
handles the pairs whose sides have different kinds, and the closed same-kind statement the
others. -/
theorem osinLemma94CaseOneInput_closed : OsinLemma94CaseOneInput.{u, w, v} :=
  osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk osinLemma94CaseOneSameCell

#audit_closed_axioms GroupApproximation.GGT.BaselineDischarge.osinLemma94CaseOneInput_closed

section Configuration

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **No leaf inside a `G`-face.**  In a family with the fewest darts, the walk of an unselected
`G`-face never runs from a dart straight back along its reverse. -/
theorem not_leaf_of_dartMinimal_closed
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts} (hS : S.DartMinimal)
    {f : S.diagram.toCombMap.Face} (hf : S.UnselectedGFace f) {d : S.diagram.toCombMap.Dart}
    (hd : S.diagram.toCombMap.faceOf d = f)
    (hleaf : S.diagram.toCombMap.facePerm d = S.diagram.toCombMap.alpha d) : False :=
  GloballyDistinguishedSectionFamily.not_leaf_of_dartMinimal
    GloballyDistinguishedSectionFamily.pendantPathRemovalInput hS hf hd hleaf

#audit_axioms GroupApproximation.GGT.BaselineDischarge.not_leaf_of_dartMinimal_closed

/-- **A cutting chain has no dart together with its reverse**, in a family with the fewest
darts. -/
theorem alpha_not_mem_of_dartMinimal_closed
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts} (hS : S.DartMinimal)
    {f : S.diagram.toCombMap.Face} (hf : S.UnselectedGFace f) {r : ℕ}
    {chain rest : List S.diagram.toCombMap.Dart}
    (hwalk : (S.diagram.faceBoundary f).darts.rotate r = chain ++ rest)
    (hjoints : S.RunsBackAcross chain) :
    ∀ d ∈ chain, S.diagram.toCombMap.alpha d ∉ chain :=
  GloballyDistinguishedSectionFamily.alpha_not_mem_of_dartMinimal
    GloballyDistinguishedSectionFamily.pendantPathRemovalInput hS hf hwalk hjoints

#audit_axioms GroupApproximation.GGT.BaselineDischarge.alpha_not_mem_of_dartMinimal_closed

/-- **One backwards connector pair of Case 2.**  "This contradicts our assumption that
`∑ l(t_i)` is minimal."  Once `ε ≥ 3`, a family with the fewest darts has no backwards connector
pair of polygon `k` whose target side is a cutting path. -/
theorem osinLemma94CaseTwo_false_closed (heps : 3 ≤ eps)
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts} (hS : S.DartMinimal)
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (P.corner k) (P.word k) (P.sideCount k)
      (P.relatorSides k) (P.longSides k) eps)
    (hback : C.b' < C.b) (hcut : P.kind k C.target = .cutting) : False :=
  osinLemma94CaseTwo_false GloballyDistinguishedSectionFamily.separatedCornerInsertionInput heps
    hS P k C hback hcut

#audit_axioms GroupApproximation.GGT.BaselineDischarge.osinLemma94CaseTwo_false_closed

end Configuration

end GroupApproximation.GGT.BaselineDischarge
