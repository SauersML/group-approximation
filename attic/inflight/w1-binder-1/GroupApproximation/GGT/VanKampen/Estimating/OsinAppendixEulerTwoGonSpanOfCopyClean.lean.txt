import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonEulerSpan
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonCopyCleanWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerSection
import GroupApproximation.Meta.AxiomGuard

/-!
# The Euler span input of a two-gon from the edge conditions

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

`twoGonHoldsInput_of_eulerSpan` (`Estimating/OsinAppendixEulerTwoGonEulerSpan`) derives C6′ from
`TwoGonEulerSpanInput`: a noncrossing decomposition walk with the gap equation of its source span,
the ends of its target span, and the Euler equalities of its two reclosings.  Under the edge
conditions `PocketWalk.CopyCleanAt`, the pocket walk of `PocketWalk.exists_of_le` gives the walk,
the gap equation and the ends (lane `ms-inverses-2`, `exists_noncrossing_decomposition_of_copyCleanAt`,
which keeps only the length bounds).  So the input splits into the edge conditions on the labels of
the two-gon and the Euler equalities of that walk.

* `PocketWalk.exists_noncrossing_decomposition_gap_of_copyCleanAt`: the decomposition walk under the
  edge conditions, with the gap equation and the ends of the target span.
* `TwoGonCopyCleanInput`: the edge conditions for the labels of a two-gon (named residual).
* `TwoGonDecompositionEulerInput`: for exterior regions of one cell to one section under the edge
  conditions, both reclosings of a noncrossing decomposition walk with those spans keep the Euler
  characteristic (named residual).
* `twoGonEulerSpanInput_of_copyCleanAt`, `twoGonHoldsInput_of_copyCleanEuler`: `TwoGonEulerSpanInput`
  and `TwoGonHoldsInput` from the two residuals.
* `OsinTwoGonCopyCleanSectionStatement`, `OsinTwoGonDecompositionEulerSectionStatement`,
  `osinTwoGonHoldsSection_of_copyCleanEuler`: the same uniformly in the parameters, in the preamble
  of `OsinTwoGonHoldsSectionStatement`.

The edge conditions are asked on the given family.  Outer spurs and shared edges can break them
there; the copy route (`TwoGonEitherFollowsCopyInput`) passes to another family instead.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7, through Osin's Lemma 9.7(a));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides Surgery.MapCollapse

namespace PocketWalk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The decomposition walk under the edge conditions, with its spans.**  Let `a ≠ b` be exterior
regions of the cell `i` to the section `j`, with the target arc of `a` ending before that of `b`
starts.  If the diagram has least area and satisfies the edge conditions for `a` and `b` from `i`,
there are a source arc and a target arc with `source.reverseDarts ++ a.rightSide ++ target.darts ++
b.leftSide` a noncrossing closed walk, the source arc the source arc of `a`, a gap arc and the
source arc of `b`, and the target arc from the start of the target arc of `a` to the end of that of
`b`. -/
theorem exists_noncrossing_decomposition_gap_of_copyCleanAt
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ RegionCandidate.exteriorAt S.family i)
    (hb : b ∈ RegionCandidate.exteriorAt S.family i) (hab : a ≠ b)
    (hja : RegionCandidate.TargetsSectionIndex cuts j a)
    (hjb : RegionCandidate.TargetsSectionIndex cuts j b)
    (horder : a.2.targetArc.start.1 + a.2.targetArc.length ≤ b.2.targetArc.start.1)
    (hlea : S.diagram.LeastArea) (hclean : CopyCleanAt S.diagram i a b) :
    ∃ (source : CyclicArc (cellDarts S.diagram i))
      (target : CyclicArc (targetDarts S.diagram none)),
      IsNoncrossingClosedWalk S.diagram.toCombMap
          (source.reverseDarts ++ a.2.rightSide ++ target.darts ++ b.2.leftSide) ∧
        (∃ gap : CyclicArc (cellDarts S.diagram i),
          source.darts = a.2.sourceArc.darts ++ gap.darts ++ b.2.sourceArc.darts) ∧
        target.start.1 = a.2.targetArc.start.1 ∧
        target.start.1 + target.length = b.2.targetArc.start.1 + b.2.targetArc.length := by
  obtain ⟨K, hsource, hfirst, hsecond, ⟨Gap, hsrc⟩, hstart, hend⟩ :=
    exists_of_le S ha hb hab hja hjb (by omega)
  have hw := isNoncrossingClosedWalk_of_copyClean S ha hb hab hjb K hsource hfirst hsecond
    ⟨Gap, hsrc⟩ hstart hend hlea (copyClean_of_copyCleanAt K hsource hclean)
  rcases K with ⟨src, sArc, tArc, fs, ss, _, _, _, _, _, _, _, _⟩
  dsimp only at hsource hfirst hsecond hsrc hstart hend hw
  subst hsource hfirst hsecond
  refine ⟨sArc, tArc, ?_, ⟨Gap, hsrc⟩, hstart, hend⟩
  have hrot : IsNoncrossingClosedWalk S.diagram.toCombMap
      (b.2.leftSide ++ (invDarts S.diagram sArc.darts ++ a.2.rightSide ++ tArc.darts)) := by
    simpa only [PocketWalk.walk, List.append_assoc] using hw
  exact hrot.append_comm

end PocketWalk

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The edge conditions for the labels of a two-gon** (named residual).  For the labels of a
two-gon of `phiMapO` with no corner in its gap and no relator cell, exterior regions `a ≠ b` of one
cell `i` to one section `j`, target arc of `a` first, the optimal diagram satisfies the edge
conditions for `a` and `b` from `i`. -/
def TwoGonCopyCleanInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        S.NoLoops → S.NoMultipleEdges →
          ∀ a₀ ∈ S.family, a₀.2.target = none →
            ∀ (P : RegionCandidate.ExtPhiData S.family
                (RegionCandidate.linkedComponentO S.family a₀))
              (f : (RegionCandidate.phiMapO S.family
                (RegionCandidate.linkedComponentO S.family a₀)).Face),
              (RegionCandidate.phiSubdividedMultigraphO P).IsTwoGon f →
              ¬RegionCandidate.GapAtOHoldsCorner cuts S.family
                (RegionCandidate.linkedComponentO S.family a₀) f →
              ¬RegionCandidate.HoldsCellO S.family
                (RegionCandidate.linkedComponentO S.family a₀) f →
              ∀ (i : Fin S.diagram.rCellCount) (j : Fin cuts.count),
                ∀ a ∈ RegionCandidate.exteriorAt S.family i,
                  ∀ b ∈ RegionCandidate.exteriorAt S.family i, a ≠ b →
                    RegionCandidate.TargetsSectionIndex cuts j a →
                      RegionCandidate.TargetsSectionIndex cuts j b →
                        a.2.targetArc.start.1 + a.2.targetArc.length ≤
                          b.2.targetArc.start.1 →
                          PocketWalk.CopyCleanAt S.diagram i a b

/-- **The Euler equalities of the decomposition walk** (named residual).  For a least-area optimal
diagram, exterior regions `a ≠ b` of one cell `i` to one section `j`, target arc of `a` first, under
the edge conditions from `i`: every noncrossing walk
`source.reverseDarts ++ a.rightSide ++ target.darts ++ b.leftSide` whose source span is the source
arc of `a`, a gap arc and the source arc of `b`, and whose target span runs from the start of the
target arc of `a` to the end of that of `b`, keeps the Euler characteristic under both reclosings. -/
def TwoGonDecompositionEulerInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts), S.diagram.LeastArea →
      ∀ (i : Fin S.diagram.rCellCount) (j : Fin cuts.count) (a b : RegionCandidate D eps S.diagram),
        a ∈ RegionCandidate.exteriorAt S.family i → b ∈ RegionCandidate.exteriorAt S.family i →
          a ≠ b → RegionCandidate.TargetsSectionIndex cuts j a →
            RegionCandidate.TargetsSectionIndex cuts j b →
              a.2.targetArc.start.1 + a.2.targetArc.length ≤ b.2.targetArc.start.1 →
                PocketWalk.CopyCleanAt S.diagram i a b →
                  ∀ (source : CyclicArc (cellDarts S.diagram i))
                    (target : CyclicArc (targetDarts S.diagram none))
                    (hw : IsNoncrossingClosedWalk S.diagram.toCombMap
                      (source.reverseDarts ++ a.2.rightSide ++ target.darts ++ b.2.leftSide)),
                    (∃ gap : CyclicArc (cellDarts S.diagram i),
                      source.darts = a.2.sourceArc.darts ++ gap.darts ++ b.2.sourceArc.darts) →
                      target.start.1 = a.2.targetArc.start.1 →
                        target.start.1 + target.length =
                            b.2.targetArc.start.1 + b.2.targetArc.length →
                          (reclosedMap S.diagram.toCombMap
                              (sideFaces S.diagram.toCombMap
                                (source.reverseDarts ++ a.2.rightSide ++ target.darts ++
                                  b.2.leftSide))
                              (hw.innerCycle S.diagram.planar)).eulerCharacteristic =
                              S.diagram.toCombMap.eulerCharacteristic ∧
                            (reclosedMap S.diagram.toCombMap
                                (sideOutside S.diagram.toCombMap
                                  (source.reverseDarts ++ a.2.rightSide ++ target.darts ++
                                    b.2.leftSide))
                                (hw.outerCycle S.diagram.planar)).eulerCharacteristic =
                              S.diagram.toCombMap.eulerCharacteristic

/-- **The Euler span input from the edge conditions and the Euler equalities.** -/
theorem twoGonEulerSpanInput_of_copyCleanAt {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (hclean : TwoGonCopyCleanInput.{u, w, v} D lambda c eps W)
    (heuler : TwoGonDecompositionEulerInput.{u, w, v} D lambda c eps W) :
    TwoGonEulerSpanInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell i j a ha b hb hab hja hjb
    horder
  have hleaS : S.diagram.LeastArea := S.equiv.leastArea hlea
  have hcc := hclean Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell i j a ha b hb
    hab hja hjb horder
  obtain ⟨source, target, hw, hgap, hstart, hend⟩ :=
    PocketWalk.exists_noncrossing_decomposition_gap_of_copyCleanAt S.toRealizedSectionFamily ha hb
      hab hja hjb horder hleaS hcc
  exact ⟨source, target, hw,
    heuler Delta cuts S hleaS i j a b ha hb hab hja hjb horder hcc source target hw hgap hstart hend,
    hgap, hstart, hend⟩

/-- **C6′ from the edge conditions and the Euler equalities.** -/
theorem twoGonHoldsInput_of_copyCleanEuler {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (hclean : TwoGonCopyCleanInput.{u, w, v} D lambda c eps W)
    (heuler : TwoGonDecompositionEulerInput.{u, w, v} D lambda c eps W) :
    TwoGonHoldsInput.{u, w, v} D lambda c eps W :=
  twoGonHoldsInput_of_eulerSpan (twoGonEulerSpanInput_of_copyCleanAt hclean heuler)

/-- **The edge conditions for two-gons, uniformly in the parameters** (named residual), in the
preamble of `OsinTwoGonHoldsSectionStatement`. -/
def OsinTwoGonCopyCleanSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              TwoGonCopyCleanInput.{u, w, v} D lambda c eps W

/-- **The Euler equalities of decomposition walks, uniformly in the parameters** (named residual),
in the preamble of `OsinTwoGonHoldsSectionStatement`. -/
def OsinTwoGonDecompositionEulerSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              TwoGonDecompositionEulerInput.{u, w, v} D lambda c eps W

/-- **C6′, uniformly in the parameters, from the edge conditions and the Euler equalities.**  `ε₀`
and `ρ₀` are the larger of the two. -/
theorem osinTwoGonHoldsSection_of_copyCleanEuler
    (hclean : OsinTwoGonCopyCleanSectionStatement.{u, w, v})
    (heuler : OsinTwoGonDecompositionEulerSectionStatement.{u, w, v}) :
    OsinTwoGonHoldsSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsK, hK⟩ := hclean D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsT, hT⟩ := heuler D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨max epsK epsT, fun eps heps => ?_⟩
  obtain ⟨hepsK, hepsT⟩ := max_le_iff.mp heps
  obtain ⟨rhoK, hrhoKpos, hKrho⟩ := hK eps hepsK
  obtain ⟨rhoT, -, hTrho⟩ := hT eps hepsT
  refine ⟨max rhoK rhoT, lt_of_lt_of_le hrhoKpos (le_max_left _ _),
    fun rho hrho W hcondition => ?_⟩
  obtain ⟨hrhoK, hrhoT⟩ := max_le_iff.mp hrho
  exact twoGonHoldsInput_of_copyCleanEuler (hKrho rho hrhoK W hcondition)
    (hTrho rho hrhoT W hcondition)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.exists_noncrossing_decomposition_gap_of_copyCleanAt
#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonCopyCleanInput
#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonDecompositionEulerInput
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonEulerSpanInput_of_copyCleanAt
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonHoldsInput_of_copyCleanEuler
#audit_axioms GroupApproximation.GGT.VanKampen.OsinTwoGonCopyCleanSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.OsinTwoGonDecompositionEulerSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.osinTwoGonHoldsSection_of_copyCleanEuler
