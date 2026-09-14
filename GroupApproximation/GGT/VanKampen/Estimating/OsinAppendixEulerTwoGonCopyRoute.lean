import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonSpanOfCopyClean
import GroupApproximation.Meta.AxiomGuard

/-!
# C6′ for two-gon pockets through a clean copy

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

`twoGonHoldsInput_of_copyCleanEuler` (`Estimating/OsinAppendixEulerTwoGonSpanOfCopyClean`) asks for
the edge conditions `PocketWalk.CopyCleanAt` on the given family.  Four of them are global predicates
on the optimal diagram: no outer spur, no edge between a relator cell and the exterior, no side dart
along the exterior, and no edge joining two regions.  Least area excludes none of them, and the
closed surgeries `outerSpurThickening`, `outerCellThickening`, `outerSideThickening` and
`regionPairThickening` remove them only on O-equivalent copies.  So the edge conditions are asked
on a copy carrying a two-gon instead.

* `TwoGonHoldsCleanInput`: C6′ for two-gons all of whose label pairs satisfy the edge conditions.
* `twoGonHoldsCleanInput_of_decompositionEuler`: it follows from the Euler equalities of the
  decomposition walk.
* `TwoGonCleanCopyInput`: every two-gon of a least-area optimal family has a two-gon, with no corner
  in its gap and no relator cell, on some optimal family over the same diagram and cuts, all of whose
  label pairs satisfy the edge conditions (named residual).
* `twoGonCleanCopyInput_of_copyCleanInput`: the given-family form implies it, with the same family.
* `twoGonHoldsInput_of_cleanCopy`, `twoGonHoldsInput_of_cleanCopyEuler`: C6′ from the copy and the
  Euler equalities.
* `OsinTwoGonCleanCopySectionStatement`, `osinTwoGonHoldsSection_of_cleanCopyEuler`: the same
  uniformly in the parameters.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7, through Osin's Lemma 9.7(a));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **C6′ for clean two-gons.**  The binders of `TwoGonHoldsInput`, when every label pair of the
two-gon satisfies the edge conditions, give a contradiction. -/
def TwoGonHoldsCleanInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
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
              (∀ (i : Fin S.diagram.rCellCount) (j : Fin cuts.count),
                ∀ a ∈ RegionCandidate.exteriorAt S.family i,
                  ∀ b ∈ RegionCandidate.exteriorAt S.family i, a ≠ b →
                    RegionCandidate.TargetsSectionIndex cuts j a →
                      RegionCandidate.TargetsSectionIndex cuts j b →
                        a.2.targetArc.start.1 + a.2.targetArc.length ≤
                          b.2.targetArc.start.1 →
                          PocketWalk.CopyCleanAt S.diagram i a b) →
              False

/-- **C6′ for clean two-gons from the Euler equalities.**  The edge conditions of the labels give the
decomposition walk with its spans, and the rest is the argument of `twoGonHoldsInput_of_eulerSpan`
at the given family. -/
theorem twoGonHoldsCleanInput_of_decompositionEuler {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (heuler : TwoGonDecompositionEulerInput.{u, w, v} D lambda c eps W) :
    TwoGonHoldsCleanInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell hclean
  obtain ⟨y, hy, hyf, hnone, h4, j, hya, hyb, hab, hja, hjb, horder⟩ :=
    RegionCandidate.exists_twoGonLabels S hmulti P hf hcorner
  have hleaS : S.diagram.LeastArea := S.equiv.leastArea hlea
  have hcc := hclean _ j _ hya _ hyb hab hja hjb horder
  obtain ⟨source, target, hw, ⟨gap, hgap⟩, hstart, hend⟩ :=
    PocketWalk.exists_noncrossing_decomposition_gap_of_copyCleanAt S.toRealizedSectionFamily hya
      hyb hab hja hjb horder hleaS hcc
  have heul := heuler Delta cuts S hleaS _ j _ _ hya hyb hab hja hjb horder hcc source target hw
    ⟨gap, hgap⟩ hstart hend
  have H := RegionCandidate.twoGonClassHyp_of_linkedComponent S P hcell hy hyf hnone h4 hyb
  have hnondegA := S.nondegenerate _ (Finset.mem_filter.mp (Finset.mem_filter.mp hya).1).1
  have hnondegB := S.nondegenerate _ (Finset.mem_filter.mp (Finset.mem_filter.mp hyb).1).1
  have hlen := congrArg List.length hgap
  simp only [List.length_append, CyclicArc.darts_length] at hlen
  have hL : (S.diagram.faceBoundary S.diagram.outerFace).darts.length =
      Delta.boundaryWord.length := by
    rw [← S.equiv.boundaryWord_eq, ← dartWord_outerDarts S.diagram, dartWord, List.length_map,
      outerDarts, List.length_map, List.length_reverse]
  have hbound : ∀ x ∈ RegionCandidate.linkedComponentO S.family a₀, x.2.target = none →
      x.2.targetArc.start.1 + x.2.targetArc.length ≤
        (S.diagram.faceBoundary S.diagram.outerFace).darts.length := by
    intro x hx hxt
    obtain ⟨j', -, -, hj'⟩ := (S.respects x (P.subset hx)).2 hxt
    rw [hL]
    exact hj'.trans (cuts.cut_le_length j'.succ)
  have hLo : (targetDarts S.diagram none).length = Delta.boundaryWord.length := by
    rw [← hL]
    simp only [targetDarts, outerDarts, List.length_map, List.length_reverse]
  have hY : target.start.1 + target.length ≤ (targetDarts S.diagram none).length := by
    have h1 := hjb.2.2
    have h2 := cuts.cut_le_length j.succ
    omega
  have hposS : 0 < source.length := by omega
  have hposT : 0 < target.length := by omega
  have hsrcA := RegionCandidate.twoGonSource_left source hgap
  have hsrcB := RegionCandidate.twoGonSource_right source hgap
  have htgtA := RegionCandidate.twoGonTarget_left H.target_left target hstart (by omega)
  have htgtB := RegionCandidate.twoGonTarget_right H.target_right target (by omega) hend hY
  have hsubS : ∀ d ∈ source.reverseDarts, d ∈
      source.reverseDarts ++ (RegionCandidate.phiRegionO y).2.rightSide ++ target.darts ++
        (RegionCandidate.phiRegionO ((RegionCandidate.phiMapO S.family
          (RegionCandidate.linkedComponentO S.family a₀)).facePerm
            ((RegionCandidate.phiMapO S.family
              (RegionCandidate.linkedComponentO S.family a₀)).facePerm y))).2.leftSide :=
    fun _ hd => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hd))
  have hsubT : ∀ d ∈ target.darts, d ∈
      source.reverseDarts ++ (RegionCandidate.phiRegionO y).2.rightSide ++ target.darts ++
        (RegionCandidate.phiRegionO ((RegionCandidate.phiMapO S.family
          (RegionCandidate.linkedComponentO S.family a₀)).facePerm
            ((RegionCandidate.phiMapO S.family
              (RegionCandidate.linkedComponentO S.family a₀)).facePerm y))).2.leftSide :=
    fun _ hd => List.mem_append_left _ (List.mem_append_right _ hd)
  have hout := outerFace_not_mem_sideFaces_of_target_mem hw target hposT hsubT
  have hcoff := cellFace_not_mem_sideFaces_of_source_mem hw source hposS hsubS
  have Hs := RegionCandidate.TwoGonWalkSideHyp.mk
    (RegionCandidate.twoGonWalk_left_side source target H.target_left hsrcA htgtA)
    (RegionCandidate.twoGonWalk_right_side source target H.target_right hsrcB htgtB)
    hout hcoff
  have hbase := RegionCandidate.twoGonPocketFace_of_mem_decomposition (family := S.family)
    (E := RegionCandidate.linkedComponentO S.family a₀) (x := y.1) source target
    H.target_left H.target_right
    (fun p hp hpa hpb => by
      have hαp : S.diagram.toCombMap.alpha p ∈ source.reverseDarts := by
        simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
        exact ⟨p, hp, rfl⟩
      have hmem := (mem_sideFaces_iff _ _ _).mpr ⟨_, hsubS _ hαp, Relation.EqvGen.refl _⟩
      have hp' := hp
      rw [hgap, List.mem_append, List.mem_append] at hp'
      rcases hp' with (h | h) | h
      · exact absurd h hpa
      · exact RegionCandidate.twoGonPocketFace_of_cellGap P hy hnone H source hgap h
          (fun hh => hout (hh ▸ hmem)) (fun hh => hcoff (hh ▸ hmem))
      · exact absurd h hpb)
    (RegionCandidate.twoGonPocketFace_of_targetSpan P hbound hy hnone h4 H target hstart hend hY
      (fun d hd =>
        ⟨fun hh => hout (hh ▸ (mem_sideFaces_iff _ _ d).mpr ⟨d, hsubT d hd, Relation.EqvGen.refl _⟩),
          fun hh => hcoff
            (hh ▸ (mem_sideFaces_iff _ _ d).mpr ⟨d, hsubT d hd, Relation.EqvGen.refl _⟩)⟩))
  have hno := P.cell_face_not_mem_sideFaces_of_twoGon_of_base H Hs hbase
    (fun k v hv hface => by
      by_contra hk
      exact hcell ⟨k, hk, y, hyf, v, hv, hface⟩)
  have hcells : ∀ C ∈ S.diagram.relatorCells, C.face ∉ sideFaces S.diagram.toCombMap
      (source.reverseDarts ++ (RegionCandidate.phiRegionO y).2.rightSide ++ target.darts ++
        (RegionCandidate.phiRegionO ((RegionCandidate.phiMapO S.family
          (RegionCandidate.linkedComponentO S.family a₀)).facePerm
            ((RegionCandidate.phiMapO S.family
              (RegionCandidate.linkedComponentO S.family a₀)).facePerm y))).2.leftSide) := by
    intro C hC
    obtain ⟨n, rfl⟩ := List.mem_iff_get.mp hC
    exact hno n
  exact S.false_of_mergeDisc hya hyb hab hja hjb
    (Surgery.InnerDiscRegion.ofPocketRegion
      (PocketRegion.ofNoncrossingClosedWalkEuler hw hout heul.1 heul.2) hcells)
    source target (k := 0) (List.rotate_zero _)
    (fun _ hx hxa hxb => P.disjoint_sideFaces_of_twoGon_of_base H Hs hbase hx hxa hxb)
    (by omega) hstart hend (by omega)

/-- **A two-gon on a clean copy** (named residual).  For every two-gon of `phiMapO` with no corner in
its gap and no relator cell, of a least-area optimal family, some optimal family over the same
diagram and cuts has no loops and no multiple edges and carries a two-gon with no corner in its gap
and no relator cell, all of whose label pairs satisfy the edge conditions. -/
def TwoGonCleanCopyInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
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
              ∃ S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S'.NoLoops ∧ S'.NoMultipleEdges ∧
                  ∃ a₀' ∈ S'.family, a₀'.2.target = none ∧
                    ∃ (P' : RegionCandidate.ExtPhiData S'.family
                        (RegionCandidate.linkedComponentO S'.family a₀'))
                      (f' : (RegionCandidate.phiMapO S'.family
                        (RegionCandidate.linkedComponentO S'.family a₀')).Face),
                      (RegionCandidate.phiSubdividedMultigraphO P').IsTwoGon f' ∧
                        ¬RegionCandidate.GapAtOHoldsCorner cuts S'.family
                          (RegionCandidate.linkedComponentO S'.family a₀') f' ∧
                        ¬RegionCandidate.HoldsCellO S'.family
                          (RegionCandidate.linkedComponentO S'.family a₀') f' ∧
              ∀ (i : Fin S'.diagram.rCellCount) (j : Fin cuts.count),
                ∀ a ∈ RegionCandidate.exteriorAt S'.family i,
                  ∀ b ∈ RegionCandidate.exteriorAt S'.family i, a ≠ b →
                    RegionCandidate.TargetsSectionIndex cuts j a →
                      RegionCandidate.TargetsSectionIndex cuts j b →
                        a.2.targetArc.start.1 + a.2.targetArc.length ≤
                          b.2.targetArc.start.1 →
                          PocketWalk.CopyCleanAt S'.diagram i a b

/-- **The given-family edge conditions give a clean copy**: the same family. -/
theorem twoGonCleanCopyInput_of_copyCleanInput {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (hclean : TwoGonCopyCleanInput.{u, w, v} D lambda c eps W) :
    TwoGonCleanCopyInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell
  exact ⟨S, hloops, hmulti, a₀, ha₀, hat, P, f, hf, hcorner, hcell,
    hclean Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell⟩

/-- **C6′ from a clean copy.** -/
theorem twoGonHoldsInput_of_cleanCopy {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (hcopy : TwoGonCleanCopyInput.{u, w, v} D lambda c eps W)
    (hclean : TwoGonHoldsCleanInput.{u, w, v} D lambda c eps W) :
    TwoGonHoldsInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell
  obtain ⟨S', hloops', hmulti', a₀', ha₀', hat', P', f', hf', hcorner', hcell', hcc⟩ :=
    hcopy Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell
  exact hclean Delta cuts hlea S' hloops' hmulti' a₀' ha₀' hat' P' f' hf' hcorner' hcell' hcc

/-- **C6′ from a clean copy and the Euler equalities.** -/
theorem twoGonHoldsInput_of_cleanCopyEuler {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (hcopy : TwoGonCleanCopyInput.{u, w, v} D lambda c eps W)
    (heuler : TwoGonDecompositionEulerInput.{u, w, v} D lambda c eps W) :
    TwoGonHoldsInput.{u, w, v} D lambda c eps W :=
  twoGonHoldsInput_of_cleanCopy hcopy (twoGonHoldsCleanInput_of_decompositionEuler heuler)

/-- **Clean copies of two-gons, uniformly in the parameters** (named residual), in the preamble of
`OsinTwoGonHoldsSectionStatement`. -/
def OsinTwoGonCleanCopySectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              TwoGonCleanCopyInput.{u, w, v} D lambda c eps W

/-- **C6′, uniformly in the parameters, from clean copies and the Euler equalities.**  `ε₀` and `ρ₀`
are the larger of the two. -/
theorem osinTwoGonHoldsSection_of_cleanCopyEuler
    (hcopy : OsinTwoGonCleanCopySectionStatement.{u, w, v})
    (heuler : OsinTwoGonDecompositionEulerSectionStatement.{u, w, v}) :
    OsinTwoGonHoldsSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsK, hK⟩ := hcopy D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsT, hT⟩ := heuler D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨max epsK epsT, fun eps heps => ?_⟩
  obtain ⟨hepsK, hepsT⟩ := max_le_iff.mp heps
  obtain ⟨rhoK, hrhoKpos, hKrho⟩ := hK eps hepsK
  obtain ⟨rhoT, -, hTrho⟩ := hT eps hepsT
  refine ⟨max rhoK rhoT, lt_of_lt_of_le hrhoKpos (le_max_left _ _),
    fun rho hrho W hcondition => ?_⟩
  obtain ⟨hrhoK, hrhoT⟩ := max_le_iff.mp hrho
  exact twoGonHoldsInput_of_cleanCopyEuler (hKrho rho hrhoK W hcondition)
    (hTrho rho hrhoT W hcondition)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonHoldsCleanInput
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonHoldsCleanInput_of_decompositionEuler
#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonCleanCopyInput
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonCleanCopyInput_of_copyCleanInput
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonHoldsInput_of_cleanCopy
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonHoldsInput_of_cleanCopyEuler
#audit_axioms GroupApproximation.GGT.VanKampen.OsinTwoGonCleanCopySectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.osinTwoGonHoldsSection_of_cleanCopyEuler
