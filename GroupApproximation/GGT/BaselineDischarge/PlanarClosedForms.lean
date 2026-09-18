import GroupApproximation.GGT.BaselineDischarge.SurgeryPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94Pieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94AntiparallelMetric
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonRealization
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CellArcs
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BoundaryArcs
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOneFace
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PinchedQuadrilateral
import GroupApproximation.Meta.AxiomGuard

/-!
# Closed forms of the planar half of Lemma 9.4

Osin (math/0411039v3, Appendix), Lemma 9.4: "Let `S` denote the sum of lengths of all unbound
arcs of type (A1) in `Δ`.  Then `S < n √ρ`."  Some lemmas of the planar half take as hypothesis
a statement that is already proved, or one of its instances.  This file supplies them.

Route.

* `planarPolygons_unbound_lt_closed`: the contradiction at fixed parameters,
  `OsinLemma94PlanarPolygons.unbound_lt`, with the metric premise at every threshold taken from
  the closed metric half `osinLemma94AntiparallelMetric`.  The thresholds for `ε` and `ρ` are
  those of the metric half.
* `cellArcsQuasiGeodesic_of_cCondition`, `boundaryArcsQuasiGeodesic_of_nonneg`,
  `cuttingChainsQuasiGeodesic_of_dartMinimal`: the three arc predicates of the polygon
  realization, from the closed `osinLemma94CellArcsInput_holds`, `osinLemma94BoundaryArcsInput`
  and `osinLemma94CuttingChainsInput_closed`, over the regime hypotheses of those statements.
* `false_of_quadrilateral_closed`: Case 1 with one piece per arc ("This contradicts the
  maximality of `M`"), from `RealizedSectionFamily.false_of_quadrilateral_face` on the optimal
  family, with neither `OsinLemma94PinchedQuadrilateralStatement` nor least area.

## Manuscript status
Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 4.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.BaselineDischarge

universe u w v

open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded

/-- **The unbound sum is below `n √ρ`, at the metric thresholds.**  "Assume that `S ≥ n √ρ`."
For a four-point hyperbolic `Γ(G, A)`, `0 < λ` and `0 ≤ c`, there is a threshold for `ε` and,
for each `ε` above it and each side constant `K`, a positive threshold for `ρ` such that every
family of component polygons with at most `K n` sides has unbound sum below `n √ρ`. -/
theorem planarPolygons_unbound_lt_closed {G : Type u} [Group G] {Lambda : Type w}
    (D : RelGenSet G Lambda)
    (hhyper : ∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (lambda c : ℝ) (hlambda : 0 < lambda) (hc : 0 ≤ c) :
    ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps → ∀ K : ℕ,
      ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
        ∀ {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
          {cuts : SectionCuts D lambda c Delta.boundaryWord}
          {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts},
          OsinLemma94PlanarPolygons D lambda c eps K S → 0 < Delta.rCellCount →
            (∑ i : Fin S.diagram.rCellCount,
                ((RegionCandidate.unboundDarts S.family i).card : ℝ)) <
              (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ) := by
  obtain ⟨eps0, hmetric⟩ := osinLemma94AntiparallelMetric D hhyper lambda c hlambda hc
  refine ⟨eps0, ?_⟩
  intro eps heps K
  obtain ⟨rho0, hrho0, hrho⟩ := hmetric eps heps K
  refine ⟨rho0, hrho0, ?_⟩
  intro rho hr W Delta cuts S P hcells
  exact P.unbound_lt hcells (hrho rho hr)

#audit_axioms GroupApproximation.GGT.BaselineDischarge.planarPolygons_unbound_lt_closed

section Configuration

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The relator arcs are quasi-geodesic** under the `C`-condition. -/
theorem cellArcsQuasiGeodesic_of_cCondition
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) {mu : ℝ} {rho : ℕ}
    (hcond : OsinCCondition D W eps mu lambda c rho) (hc : 0 ≤ c) :
    S.CellArcsQuasiGeodesic :=
  osinLemma94CellArcsInput_holds S hcond hc

#audit_axioms GroupApproximation.GGT.BaselineDischarge.cellArcsQuasiGeodesic_of_cCondition

/-- **The boundary arcs are quasi-geodesic**: an arc of `∂Δ` inside one section. -/
theorem boundaryArcsQuasiGeodesic_of_nonneg
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) (hc : 0 ≤ c) :
    S.BoundaryArcsQuasiGeodesic :=
  osinLemma94BoundaryArcsInput S hc

#audit_axioms GroupApproximation.GGT.BaselineDischarge.boundaryArcsQuasiGeodesic_of_nonneg

/-- **The cutting chains are quasi-geodesic** in a family with the fewest darts. -/
theorem cuttingChainsQuasiGeodesic_of_dartMinimal
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) (hlambda : lambda ≤ 1)
    (hc : 0 ≤ c) (hS : S.DartMinimal) :
    S.CuttingChainsQuasiGeodesic :=
  osinLemma94CuttingChainsInput_closed S hlambda hc hS

#audit_axioms GroupApproximation.GGT.BaselineDischarge.cuttingChainsQuasiGeodesic_of_dartMinimal

/-- **Case 1 with one piece per arc.**  "This contradicts the maximality of `M`."  Let `f` be an
inner face of the optimal diagram that is no relator cell and lies in no selected region, and
suppose some rotation of its walk reads `X`, a nonempty arc `q` of a different relator cell or of
`∂Δ` inside one section, `Y`, and a nonempty arc `p` of a relator cell.  If `s_1`, `s_2` are
legal words of length and norm at most `ε` with the values of `X` and `Y`, there is a
contradiction. -/
theorem false_of_quadrilateral_closed
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (hf : f ≠ S.diagram.outerFace)
    (hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f) (havoid : ∀ a ∈ S.family, f ∉ a.1)
    (source : Fin S.diagram.rCellCount) (target : Option (Fin S.diagram.rCellCount))
    (sourceArc : CyclicArc (cellDarts S.diagram source))
    (targetArc : CyclicArc (targetDarts S.diagram target))
    (X Y : List S.diagram.toCombMap.Dart) (r : ℕ)
    (htrav : (S.diagram.faceBoundary f).darts.rotate r =
      X ++ targetBoundaryDarts S.diagram target targetArc ++ Y ++ sourceArc.reverseDarts)
    (hsource : 0 < sourceArc.length) (htarget : 0 < targetArc.length)
    (hsection : target = none → ∃ j : Fin cuts.count,
      cuts.cut j.castSucc ≤ targetArc.start.val ∧
        targetArc.start.val + targetArc.length ≤ cuts.cut j.succ)
    (hloop : target ≠ some source)
    (s1 s2 : List (RelLetter G Lambda)) (hne1 : s1 ≠ []) (hne2 : s2 ≠ [])
    (hadm1 : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) s1)
    (hinv1 : ∀ l ∈ s1, (symmetricLabelAlphabet D).IsLetter (HullSC.RelWord.inv l))
    (hadm2 : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) s2)
    (hinv2 : ∀ l ∈ s2, (symmetricLabelAlphabet D).IsLetter (HullSC.RelWord.inv l))
    (hval1 : RelLetter.listVal s1 = RelLetter.listVal (dartWord S.diagram X))
    (hval2 : RelLetter.listVal s2 = RelLetter.listVal (dartWord S.diagram Y))
    (hlen1 : s1.length ≤ eps) (hlen2 : s2.length ≤ eps)
    (hnorm1 : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal s1) ≤ eps)
    (hnorm2 : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal s2) ≤ eps) :
    False :=
  RealizedSectionFamily.false_of_quadrilateral_face S.toRealizedSectionFamily
    S.label_admissible S.weight_maximal f hf hcells havoid source target sourceArc targetArc X Y r
    htrav hsource htarget hsection hloop s1 s2 hne1 hne2 hadm1 hinv1 hadm2 hinv2 hval1 hval2
    hlen1 hlen2 hnorm1 hnorm2

#audit_axioms GroupApproximation.GGT.BaselineDischarge.false_of_quadrilateral_closed

end Configuration

end GroupApproximation.GGT.BaselineDischarge
