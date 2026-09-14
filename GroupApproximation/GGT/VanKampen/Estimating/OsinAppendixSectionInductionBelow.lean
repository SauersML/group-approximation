import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixGreendlingerPocketParts
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.7 with the multiple-edge cut read below the inductive bound

Osin, arXiv:math/0411039v3, Lemma 9.7, proved "by induction on `n`, the number of `R`-cells in `Δ`".
`osinLemma97_atParameters_of_inputs` (`Estimating/OsinAppendixSectionInduction.lean`) consumes the
multiple-edge cut producer `MultipleEdgeCutInput` at the diagram of the inductive step.  There the
inductive assumption `OsinLemma97Below … Δ.rCellCount` is already in scope, and so it is at every
other use of the producer: Corollary 9.6 below the bound, the descent through section pockets, and
their assemblies.

This module threads that assumption down to the producer, additively.
* `MultipleEdgeCutBelowInput`: the producer with the premise `OsinLemma97Below … Δ.rCellCount`, and
  `MultipleEdgeCutInput.toBelow`.
* Below variants of the consumers, each changed only where the producer is applied, which now also
  receives `hbelow`:
  - `exists_elevenCell_of_below_multiBelow`;
  - `OsinSectionPocketCut.exists_large_region_multiBelow`;
  - `descentInput_of_sectionPocketCut_multiBelow`;
  - `osinLemma97_atParameters_of_inputs_multiBelow`.
* The section assemblies over the below producer: `OsinSection97InputsBelowStatement`,
  `osinLemma97Section_of_inputsBelow`, `OsinSection97PocketInputsBelowStatement`,
  `osinSection97Inputs_of_pocketInputsBelow`, `osinLemma97Section_of_pocketInputsBelow`,
  `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketInputsBelow`,
  `OsinMultipleEdgeCutBelowSectionStatement`, `OsinMultipleEdgeCutSectionStatement.toBelow`,
  `osinSection97PocketInputsBelow_of_parts` and
  `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketPartsBelow`.

The binder-5 producer of the multiple-edge cut can then use clause (b) below `Δ`, which the proper
arcs of the cell pocket walk need (`Estimating/OsinPocketMultipleEdgeCopyOrderSection.lean`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemmas 9.7 and
4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w}

/-! ## The producer below the inductive bound -/

/-- **G2, multiple edges, below the inductive bound**: two distinct selected regions joining the same
two distinct cells of a least-area diagram enclose a cut, when clause (b) of Lemma 9.7 holds below
the number of relator cells of the diagram. -/
def MultipleEdgeCutBelowInput (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea → OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        ∀ a ∈ S.family, ∀ b ∈ S.family, a ≠ b → ∀ i j : Fin S.diagram.rCellCount, i ≠ j →
          a.JoinsCells i j → b.JoinsCells i j →
            Nonempty (OsinMultipleEdgeCut D lambda c eps Delta)

/-- The producer gives the producer below the inductive bound. -/
theorem MultipleEdgeCutInput.toBelow {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    (h : MultipleEdgeCutInput.{u, w, v} D lambda c eps W) (mu : ℝ) :
    MultipleEdgeCutBelowInput.{u, w, v} D lambda c mu eps W :=
  fun Delta cuts hlea _ S a ha b hb hab i j hij hai hbi =>
    h Delta cuts hlea S a ha b hb hab i j hij hai hbi

/-! ## Corollary 9.6 and the descent, over the below producer -/

/-- **Corollary 9.6 from the inductive assumption**, over the below producer: as
`exists_elevenCell_of_below`. -/
theorem exists_elevenCell_of_below_multiBelow
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps rho : ℕ}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    (hthreshold : 1 ≤ mu * Real.sqrt (rho : ℝ))
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (hmulti : MultipleEdgeCutBelowInput.{u, w, v} D lambda c mu eps W)
    (hloop : LoopCutInput.{u, w, v} D lambda c eps W)
    (heuler : EulerCountInput.{u, w, v} D lambda c eps W)
    (h94 : UnboundInput.{u, w, v} D lambda c mu eps rho W)
    (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (hlea : Delta.LeastArea) (hcells : 0 < Delta.rCellCount)
    (hbelow : OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount) :
    ∃ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      S.NoLoops ∧ S.NoMultipleEdges ∧
        ∃ i : Fin S.diagram.rCellCount,
          (1 - 11 * mu) * ((cell S.diagram i).word.length : ℝ) <
            ∑ a ∈ RegionCandidate.exteriorAt S.family i, (a.2.sourceArc.length : ℝ) := by
  have hsimple : ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      S.NoLoops ∧ S.NoMultipleEdges := by
    intro S
    constructor
    · intro a ha hloopEq
      obtain ⟨cut⟩ := hloop Delta cuts hlea S a ha hloopEq
      exact cut.false_of_below hO52 hcondition hlambda hmu hmuUpper hrho hlarge hlea
        (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos
          cut.rCellCount_lt)
    · intro a ha b hb hab i j hai hbj
      by_cases hij : i = j
      · subst hij
        obtain ⟨cut⟩ := hloop Delta cuts hlea S a ha
          (hai.elim (fun h => h.2.trans (congrArg some h.1.symm))
            (fun h => h.2.trans (congrArg some h.1.symm)))
        exact cut.false_of_below hO52 hcondition hlambda hmu hmuUpper hrho hlarge hlea
          (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos
            cut.rCellCount_lt)
      · obtain ⟨cut⟩ := hmulti Delta cuts hlea hbelow S a ha b hb hab i j hij hai hbj
        exact cut.false_of_below hO52 hcondition hlambda hmu hmuUpper hrho hlarge hlea
          (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos
            cut.rCellCount_lt)
  obtain ⟨S⟩ := exists_globallyDistinguishedSectionFamily D lambda c eps Delta cuts
    (DiscDiagram.reduced_of_leastArea hlea) cuts.admissible
    (fun C _ => hcondition.admissible C.word C.word_mem)
  obtain ⟨hloopsS, hmultiS⟩ := hsimple S
  obtain ⟨hcard, hplanar⟩ := heuler Delta cuts hlea hcells S hloopsS hmultiS
  have hleaS : S.diagram.LeastArea := S.equiv.leastArea hlea
  have hloopsEdge : ∀ edge : RegionCandidate.InteriorEdge S.family,
      edge.val.2.source ≠ edge.target := by
    intro edge heq
    have hmem : edge.val ∈ S.family := (Finset.mem_filter.mp edge.property).1
    apply hloopsS edge.val hmem
    rw [edge.target_eq, heq]
  have hinterior := RegionCandidate.interior_total_le_of_o52 hO52 hleaS S.family
    S.pairwise hloopsEdge hplanar hcondition hlambda hmu hlarge
  have hcountEq : S.diagram.rCellCount = Delta.rCellCount := S.equiv.rCellCount_eq
  have hunbound94 := h94 Delta cuts hlea hcells hbelow S hcard
  have hunbound := RegionCandidate.unbound_total_lt_mu S.family
    (fun i => hcondition.long _ (cell S.diagram i).word_mem) hmu.le
    (by rw [← hcountEq] at hunbound94; exact hunbound94) hthreshold
  obtain ⟨i, hi⟩ := RegionCandidate.exists_large_exterior_collection S.family
    S.pairwise hinterior hunbound
  exact ⟨S, hloopsS, hmultiS, i, hi⟩

/-- **Every section pocket carries a large region to its section**, over the below producer: as
`OsinSectionPocketCut.exists_large_region`. -/
theorem OsinSectionPocketCut.exists_large_region_multiBelow
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps rho : ℕ}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    (hthreshold : 1 ≤ mu * Real.sqrt (rho : ℝ))
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (hmulti : MultipleEdgeCutBelowInput.{u, w, v} D lambda c mu eps W)
    (hloop : LoopCutInput.{u, w, v} D lambda c eps W)
    (heuler : EulerCountInput.{u, w, v} D lambda c eps W)
    (h94 : UnboundInput.{u, w, v} D lambda c mu eps rho W)
    (hpocket : SectionPocketCutInput.{u, w, v} D lambda c eps W)
    {n : ℕ} (hbelow : OsinLemma97Below.{u, w, v} D lambda c mu eps W n) :
    ∀ (m : ℕ) (Delta : DiscDiagram.{u, w, v} W)
      (cuts : SectionCuts D lambda c Delta.boundaryWord) (j : Fin cuts.count),
      Delta.LeastArea →
        ∀ cut : OsinSectionPocketCut D lambda c eps Delta cuts j,
          cut.enclosed.rCellCount = m → m < n →
            ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y),
              Nonempty (OEquivalentDiscDiagram Delta Y) ∧
                RegionCandidate.TargetsSectionIndex cuts j b ∧
                1 - 13 * mu < b.contiguityDegree := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro Delta cuts j hlea cut hm hmn
      have hbelowCut : OsinLemma97Below.{u, w, v} D lambda c mu eps W
          cut.enclosed.rCellCount := hbelow.mono (by omega)
      obtain ⟨S, _hloopsS, _hmultiS, i, h11⟩ := exists_elevenCell_of_below_multiBelow hcondition
        hlambda hmu hmuUpper hrho hlarge hthreshold hO52 hmulti hloop heuler h94 cut.enclosed
        cut.sections cut.leastArea cut.rCellCount_pos hbelowCut
      have hunique : ∀ k : Fin cut.sections.count, (k : ℕ) ≠ 3 →
          ∀ a ∈ RegionCandidate.exteriorAt S.family i,
            ∀ b ∈ RegionCandidate.exteriorAt S.family i,
              RegionCandidate.TargetsSectionIndex cut.sections k a →
                RegionCandidate.TargetsSectionIndex cut.sections k b → a = b := by
        intro k hk a ha b hb hta htb
        by_contra hab
        obtain ⟨inner⟩ := hpocket cut.enclosed cut.sections cut.leastArea S i k a ha b hb hab
          hta htb
        have hinner : inner.enclosed.rCellCount < n := by
          have hlt := inner.rCellCount_lt
          omega
        exact cut.false_of_inner hO52 hcondition hlambda hmu hmuUpper hrho hlarge hlea k hk
          inner (hbelow inner.enclosed inner.sections inner.leastArea inner.rCellCount_pos
            hinner)
      obtain ⟨j3, hj3⟩ : ∃ j3 : Fin cut.sections.count, (j3 : ℕ) = 3 :=
        ⟨⟨3, by have hc := cut.count_eq; omega⟩, rfl⟩
      have h13 := cut.toOsinExteriorDoubleCut.lastSection_total_gt hO52 hcondition hlambda hmu
        hrho hlarge hlea S.toRealizedSectionFamily i h11 hunique j3 hj3
      have hpos : (0 : ℝ) < ((cell S.diagram i).word.length : ℝ) :=
        cellWord_length_pos hcondition.toIsSmallCancellation hrho i
      by_cases hdup : ∃ a ∈ RegionCandidate.exteriorAt S.family i,
          ∃ b ∈ RegionCandidate.exteriorAt S.family i,
            RegionCandidate.TargetsSectionIndex cut.sections j3 a ∧
              RegionCandidate.TargetsSectionIndex cut.sections j3 b ∧ a ≠ b
      · obtain ⟨a, ha, b, hb, hta, htb, hab⟩ := hdup
        obtain ⟨cut'⟩ := hpocket cut.enclosed cut.sections cut.leastArea S i j3 a ha b hb hab
          hta htb
        have hlt' := cut'.rCellCount_lt
        obtain ⟨Y', b', ⟨EY'⟩, hbY', hdeg'⟩ := ih cut'.enclosed.rCellCount (by omega)
          cut.enclosed cut.sections j3 cut.leastArea cut' rfl (by omega)
        obtain ⟨Y, b'', hEY, hbY, hdegb⟩ := cut.sectionTransport j3 hj3 Y' EY' b' hbY'
        exact ⟨Y, b'', hEY, hbY, by rw [hdegb]; exact hdeg'⟩
      · have huniq3 : ∀ a ∈ RegionCandidate.exteriorAt S.family i,
            ∀ b ∈ RegionCandidate.exteriorAt S.family i,
              RegionCandidate.TargetsSectionIndex cut.sections j3 a →
                RegionCandidate.TargetsSectionIndex cut.sections j3 b → a = b := by
          intro a ha b hb hta htb
          by_contra hab
          exact hdup ⟨a, ha, b, hb, hta, htb, hab⟩
        by_contra hnone
        have hB : (0 : ℝ) ≤ (1 - 13 * mu) * ((cell S.diagram i).word.length : ℝ) :=
          (mul_pos (by linarith) hpos).le
        have hle : S.toRealizedSectionFamily.exteriorSectionLength i j3 ≤
            (1 - 13 * mu) * ((cell S.diagram i).word.length : ℝ) := by
          unfold RealizedSectionFamily.exteriorSectionLength
          refine osinPocket_sum_le_of_subsingleton hB ?_ ?_
          · intro a ha b hb
            have ha' := Finset.mem_filter.mp ha
            have hb' := Finset.mem_filter.mp hb
            exact huniq3 a ha'.1 b hb'.1 ha'.2 hb'.2
          · intro a ha
            have ha' := Finset.mem_filter.mp ha
            refine not_lt.mp fun hgt => hnone ?_
            have hcell : ((cell S.diagram a.2.source).word.length : ℝ) =
                ((cell S.diagram i).word.length : ℝ) := by
              rw [RegionCandidate.source_eq_of_mem_exteriorAt ha'.1]
            have hdeg : 1 - 13 * mu < a.contiguityDegree := by
              unfold RegionCandidate.contiguityDegree
              rw [hcell, lt_div_iff₀ hpos]
              exact hgt
            obtain ⟨Y, b, hEY, hbY, hdegb⟩ :=
              cut.sectionTransport j3 hj3 S.diagram S.equiv a ha'.2
            exact ⟨Y, b, hEY, hbY, by rw [hdegb]; exact hdeg⟩
        linarith

/-- **`DescentInput` from the section pocket producer**, over the below producer: as
`descentInput_of_sectionPocketCut`. -/
theorem descentInput_of_sectionPocketCut_multiBelow
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps rho : ℕ}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    (hthreshold : 1 ≤ mu * Real.sqrt (rho : ℝ))
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (hmulti : MultipleEdgeCutBelowInput.{u, w, v} D lambda c mu eps W)
    (hloop : LoopCutInput.{u, w, v} D lambda c eps W)
    (heuler : EulerCountInput.{u, w, v} D lambda c eps W)
    (h94 : UnboundInput.{u, w, v} D lambda c mu eps rho W)
    (hpocket : SectionPocketCutInput.{u, w, v} D lambda c eps W) :
    DescentInput.{u, w, v} D lambda c mu eps W := by
  rintro Delta cuts hlea _hcells hbelow S _hloopsS _hmultiS ⟨i, h11⟩
  by_cases hdup : ∃ j : Fin cuts.count, ∃ a ∈ RegionCandidate.exteriorAt S.family i,
      ∃ b ∈ RegionCandidate.exteriorAt S.family i,
        RegionCandidate.TargetsSectionIndex cuts j a ∧
          RegionCandidate.TargetsSectionIndex cuts j b ∧ a ≠ b
  · obtain ⟨j, a, ha, b, hb, hta, htb, hab⟩ := hdup
    obtain ⟨cut⟩ := hpocket Delta cuts hlea S i j a ha b hb hab hta htb
    obtain ⟨Y, r, ⟨EY⟩, hr, hdeg⟩ := OsinSectionPocketCut.exists_large_region_multiBelow
      hcondition hlambda hmu hmuUpper hrho hlarge hthreshold hO52 hmulti hloop heuler h94 hpocket
      hbelow cut.enclosed.rCellCount Delta cuts j hlea cut rfl cut.rCellCount_lt
    exact osinLemma97bConclusion_of_region hlea EY j r hr hdeg
  · have huniq : S.toRealizedSectionFamily.ExteriorUniqueAt i := by
      intro j a ha b hb hta htb
      by_contra hab
      exact hdup ⟨j, a, ha, b, hb, hta, htb, hab⟩
    exact ⟨S.toRealizedSectionFamily,
      osinLemma97bConclusion_of_exteriorUniqueAt S.toRealizedSectionFamily i
        (RealizedSectionFamily.exteriorLarge_of_gt_eleven S.toRealizedSectionFamily i
          hmu.le h11)
        huniq hmuUpper (cellWord_length_pos hcondition.toIsSmallCancellation hrho i)⟩

/-! ## The induction over the below producer -/

/-- **Osin's Lemma 9.7 at fixed parameters, from the named inputs**, with the multiple-edge cut
producer read below the inductive bound: as `osinLemma97_atParameters_of_inputs`, with `hbelow`
passed to the producer. -/
theorem osinLemma97_atParameters_of_inputs_multiBelow
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps rho : ℕ}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    (hthreshold : 1 ≤ mu * Real.sqrt (rho : ℝ))
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (hmulti : MultipleEdgeCutBelowInput.{u, w, v} D lambda c mu eps W)
    (hloop : LoopCutInput.{u, w, v} D lambda c eps W)
    (heuler : EulerCountInput.{u, w, v} D lambda c eps W)
    (h94 : UnboundInput.{u, w, v} D lambda c mu eps rho W)
    (hdescent : DescentInput.{u, w, v} D lambda c mu eps W) :
    ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
      Delta.LeastArea → 0 < Delta.rCellCount →
        (∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
            S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1)) ∧
          ∃ S : RealizedSectionFamily D lambda c eps Delta cuts,
            OsinLemma97bConclusion mu S := by
  have key : ∀ (n : ℕ) (Delta : DiscDiagram.{u, w, v} W)
      (cuts : SectionCuts D lambda c Delta.boundaryWord),
      Delta.rCellCount = n → Delta.LeastArea → 0 < Delta.rCellCount →
        (∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
            S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1)) ∧
          ∃ S : RealizedSectionFamily D lambda c eps Delta cuts,
            OsinLemma97bConclusion mu S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro Delta cuts hn hlea hcells
        have hbelow : OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount := by
          intro Xi cutsXi hleaXi hcellsXi hlt
          exact (ih Xi.rCellCount (by omega) Xi cutsXi rfl hleaXi hcellsXi).2
        have hsimple : ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
            S.NoLoops ∧ S.NoMultipleEdges := by
          intro S
          constructor
          · intro a ha hloopEq
            obtain ⟨cut⟩ := hloop Delta cuts hlea S a ha hloopEq
            exact cut.false_of_below hO52 hcondition hlambda hmu hmuUpper hrho hlarge hlea
              (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos
                cut.rCellCount_lt)
          · intro a ha b hb hab i j hai hbj
            by_cases hij : i = j
            · subst hij
              obtain ⟨cut⟩ := hloop Delta cuts hlea S a ha
                (hai.elim (fun h => h.2.trans (congrArg some h.1.symm))
                  (fun h => h.2.trans (congrArg some h.1.symm)))
              exact cut.false_of_below hO52 hcondition hlambda hmu hmuUpper hrho hlarge hlea
                (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos
                  cut.rCellCount_lt)
            · obtain ⟨cut⟩ := hmulti Delta cuts hlea hbelow S a ha b hb hab i j hij hai hbj
              exact cut.false_of_below hO52 hcondition hlambda hmu hmuUpper hrho hlarge hlea
                (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos
                  cut.rCellCount_lt)
        refine ⟨fun S => (heuler Delta cuts hlea hcells S (hsimple S).1 (hsimple S).2).1, ?_⟩
        obtain ⟨S⟩ := exists_globallyDistinguishedSectionFamily D lambda c eps Delta cuts
          (DiscDiagram.reduced_of_leastArea hlea) cuts.admissible
          (fun C _ => hcondition.admissible C.word C.word_mem)
        obtain ⟨hloopsS, hmultiS⟩ := hsimple S
        obtain ⟨hcard, hplanar⟩ := heuler Delta cuts hlea hcells S hloopsS hmultiS
        have hleaS : S.diagram.LeastArea := S.equiv.leastArea hlea
        have hloopsEdge : ∀ edge : RegionCandidate.InteriorEdge S.family,
            edge.val.2.source ≠ edge.target := by
          intro edge heq
          have hmem : edge.val ∈ S.family := (Finset.mem_filter.mp edge.property).1
          apply hloopsS edge.val hmem
          rw [edge.target_eq, heq]
        have hinterior := RegionCandidate.interior_total_le_of_o52 hO52 hleaS S.family
          S.pairwise hloopsEdge hplanar hcondition hlambda hmu hlarge
        have hcountEq : S.diagram.rCellCount = Delta.rCellCount := S.equiv.rCellCount_eq
        have hunbound94 := h94 Delta cuts hlea hcells hbelow S hcard
        have hunbound := RegionCandidate.unbound_total_lt_mu S.family
          (fun i => hcondition.long _ (cell S.diagram i).word_mem) hmu.le
          (by rw [← hcountEq] at hunbound94; exact hunbound94) hthreshold
        obtain ⟨i, hi⟩ := RegionCandidate.exists_large_exterior_collection S.family
          S.pairwise hinterior hunbound
        exact hdescent Delta cuts hlea hcells hbelow S hloopsS hmultiS ⟨i, hi⟩
  intro Delta cuts hlea hcells
  exact key Delta.rCellCount Delta cuts rfl hlea hcells

/-! ## The section assemblies over the below producer -/

/-- **The section inputs of Osin's Lemma 9.7, with the below producer**: as
`OsinSection97InputsStatement`, with `MultipleEdgeCutBelowInput`. -/
def OsinSection97InputsBelowStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              MultipleEdgeCutBelowInput.{u, w, v} D lambda c mu eps W ∧
                LoopCutInput.{u, w, v} D lambda c eps W ∧
                  EulerCountInput.{u, w, v} D lambda c eps W ∧
                    DescentInput.{u, w, v} D lambda c mu eps W

/-- **Osin's Lemma 9.7 at up to four sections, from O52, Lemma 9.4 and the section inputs with the
below producer**: as `osinLemma97Section_of_inputs`. -/
theorem osinLemma97Section_of_inputsBelow
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hin : OsinSection97InputsBelowStatement.{u, w, v}) :
    OsinLemma97SectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps94, h94eps⟩ := h94 D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsIn, hinEps⟩ := hin D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨max eps94 epsIn, fun eps heps => ?_⟩
  obtain ⟨rho94, hrho94pos, h94rho⟩ := h94eps eps (le_trans (le_max_left _ _) heps)
  obtain ⟨rhoIn, -, hinRho⟩ := hinEps eps (le_trans (le_max_right _ _) heps)
  obtain ⟨rhoLarge, hLarge⟩ := exists_rho_widthBudget lambda c hmu eps
  obtain ⟨rhoThr, hThr⟩ := exists_rho_muSqrt hmu
  refine ⟨max (max rho94 rhoIn) (max rhoLarge rhoThr),
    lt_of_lt_of_le hrho94pos (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun rho hrho W hcondition => ?_⟩
  obtain ⟨hleft, hright⟩ := max_le_iff.mp hrho
  obtain ⟨h1, h2⟩ := max_le_iff.mp hleft
  obtain ⟨h3, h4⟩ := max_le_iff.mp hright
  obtain ⟨hmulti, hloop, heuler, hdescent⟩ := hinRho rho h2 W hcondition
  have hunbound : UnboundInput.{u, w, v} D lambda c mu eps rho W :=
    fun Delta cuts hlea hcells hbelow S hcard =>
      h94rho rho h1 W hcondition Delta cuts hlea hcells hbelow S hcard
  exact osinLemma97_atParameters_of_inputs_multiBelow hcondition hlambda hmu hmuUpper
    (lt_of_lt_of_le hrho94pos h1) (hLarge rho h3) (hThr rho h4) hO52 hmulti hloop heuler
    hunbound hdescent

/-- **The section inputs of Osin's Lemma 9.7 with the pocket producer, over the below producer**:
as `OsinSection97PocketInputsStatement`, with `MultipleEdgeCutBelowInput`. -/
def OsinSection97PocketInputsBelowStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              MultipleEdgeCutBelowInput.{u, w, v} D lambda c mu eps W ∧
                LoopCutInput.{u, w, v} D lambda c eps W ∧
                  PhiPrimeCountInput.{u, w, v} D lambda c eps W ∧
                    SectionPocketCutInput.{u, w, v} D lambda c eps W

/-- **The descent clause from the pocket producer, over the below producer**: as
`osinSection97Inputs_of_pocketInputs`. -/
theorem osinSection97Inputs_of_pocketInputsBelow
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hin : OsinSection97PocketInputsBelowStatement.{u, w, v}) :
    OsinSection97InputsBelowStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps94, h94eps⟩ := h94 D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsIn, hinEps⟩ := hin D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨max eps94 epsIn, fun eps heps => ?_⟩
  obtain ⟨rho94, hrho94pos, h94rho⟩ := h94eps eps (le_trans (le_max_left _ _) heps)
  obtain ⟨rhoIn, -, hinRho⟩ := hinEps eps (le_trans (le_max_right _ _) heps)
  obtain ⟨rhoLarge, hLarge⟩ := exists_rho_widthBudget lambda c hmu eps
  obtain ⟨rhoThr, hThr⟩ := exists_rho_muSqrt hmu
  refine ⟨max (max rho94 rhoIn) (max rhoLarge rhoThr),
    lt_of_lt_of_le hrho94pos (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun rho hrho W hcondition => ?_⟩
  obtain ⟨hleft, hright⟩ := max_le_iff.mp hrho
  obtain ⟨h1, h2⟩ := max_le_iff.mp hleft
  obtain ⟨h3, h4⟩ := max_le_iff.mp hright
  obtain ⟨hmulti, hloop, hcount, hpocket⟩ := hinRho rho h2 W hcondition
  have heuler : EulerCountInput.{u, w, v} D lambda c eps W :=
    eulerCountInput_of_phiPrimeCount hcount
  have hunbound : UnboundInput.{u, w, v} D lambda c mu eps rho W :=
    fun Delta cuts hlea hcells hbelow S hcard =>
      h94rho rho h1 W hcondition Delta cuts hlea hcells hbelow S hcard
  exact ⟨hmulti, hloop, heuler,
    descentInput_of_sectionPocketCut_multiBelow hcondition hlambda hmu hmuUpper
      (lt_of_lt_of_le hrho94pos h1) (hLarge rho h3) (hThr rho h4) hO52 hmulti hloop heuler
      hunbound hpocket⟩

/-- **Osin's Lemma 9.7 at up to four sections, from Lemma 9.4 and the pocket inputs with the below
producer.**  O52 is `Embedded.o52LeastArea`. -/
theorem osinLemma97Section_of_pocketInputsBelow
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hin : OsinSection97PocketInputsBelowStatement.{u, w, v}) :
    OsinLemma97SectionStatement.{u, w, v} :=
  osinLemma97Section_of_inputsBelow o52LeastArea h94
    (osinSection97Inputs_of_pocketInputsBelow o52LeastArea h94 hin)

/-- **Osin's Lemma 4.4 at least-area diagrams, from Lemma 9.4 and the pocket inputs with the below
producer.** -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_pocketInputsBelow
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hin : OsinSection97PocketInputsBelowStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_osinLemma97
    (osinLemma97Section_of_pocketInputsBelow h94 hin)

/-- **G2, multiple edges, below the inductive bound, uniformly in the parameters**: as
`OsinMultipleEdgeCutSectionStatement`, with `MultipleEdgeCutBelowInput`. -/
def OsinMultipleEdgeCutBelowSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              MultipleEdgeCutBelowInput.{u, w, v} D lambda c mu eps W

/-- The multiple-edge cut section statement gives its below form, at the same thresholds. -/
theorem OsinMultipleEdgeCutSectionStatement.toBelow
    (h : OsinMultipleEdgeCutSectionStatement.{u, w, v}) :
    OsinMultipleEdgeCutBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps0, hEps⟩ := h D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hRho⟩ := hEps eps heps
  exact ⟨rho0, hrho0, fun rho hrho W hcondition => (hRho rho hrho W hcondition).toBelow mu⟩

/-- **The pocket inputs of Lemma 9.7 from the cut parts and the two producers, with the below
multiple-edge cut**: as `osinSection97PocketInputs_of_parts`. -/
theorem osinSection97PocketInputsBelow_of_parts
    (hmulti : OsinMultipleEdgeCutBelowSectionStatement.{u, w, v})
    (hloop : OsinLoopCutSectionStatement.{u, w, v})
    (hcount : OsinPhiPrimeCountSectionStatement.{u, w, v})
    (hpocket : OsinSectionPocketCutSectionStatement.{u, w, v}) :
    OsinSection97PocketInputsBelowStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsM, hM⟩ := hmulti D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsL, hL⟩ := hloop D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsC, hC⟩ := hcount D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsP, hP⟩ := hpocket D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨max (max epsM epsL) (max epsC epsP), fun eps heps => ?_⟩
  obtain ⟨hepsML, hepsCP⟩ := max_le_iff.mp heps
  obtain ⟨hepsM, hepsL⟩ := max_le_iff.mp hepsML
  obtain ⟨hepsC, hepsP⟩ := max_le_iff.mp hepsCP
  obtain ⟨rhoM, hrhoMpos, hMrho⟩ := hM eps hepsM
  obtain ⟨rhoL, -, hLrho⟩ := hL eps hepsL
  obtain ⟨rhoC, -, hCrho⟩ := hC eps hepsC
  obtain ⟨rhoP, -, hPrho⟩ := hP eps hepsP
  refine ⟨max (max rhoM rhoL) (max rhoC rhoP),
    lt_of_lt_of_le hrhoMpos (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun rho hrho W hcondition => ?_⟩
  obtain ⟨hrhoML, hrhoCP⟩ := max_le_iff.mp hrho
  obtain ⟨hrhoM, hrhoL⟩ := max_le_iff.mp hrhoML
  obtain ⟨hrhoC, hrhoP⟩ := max_le_iff.mp hrhoCP
  exact ⟨hMrho rho hrhoM W hcondition, hLrho rho hrhoL W hcondition,
    hCrho rho hrhoC W hcondition, hPrho rho hrhoP W hcondition⟩

/-- **Osin's Lemma 4.4 at least-area diagrams, from Lemma 9.4, the cut parts with the below
multiple-edge cut, and the two producers**: as `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts`. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_pocketPartsBelow
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hmulti : OsinMultipleEdgeCutBelowSectionStatement.{u, w, v})
    (hloop : OsinLoopCutSectionStatement.{u, w, v})
    (hcount : OsinPhiPrimeCountSectionStatement.{u, w, v})
    (hpocket : OsinSectionPocketCutSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_pocketInputsBelow h94
    (osinSection97PocketInputsBelow_of_parts hmulti hloop hcount hpocket)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.MultipleEdgeCutBelowInput
#audit_axioms GroupApproximation.GGT.VanKampen.MultipleEdgeCutInput.toBelow
#audit_axioms GroupApproximation.GGT.VanKampen.exists_elevenCell_of_below_multiBelow
#audit_axioms GroupApproximation.GGT.VanKampen.OsinSectionPocketCut.exists_large_region_multiBelow
#audit_axioms GroupApproximation.GGT.VanKampen.descentInput_of_sectionPocketCut_multiBelow
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma97_atParameters_of_inputs_multiBelow
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma97Section_of_inputsBelow
#audit_axioms GroupApproximation.GGT.VanKampen.osinSection97Inputs_of_pocketInputsBelow
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma97Section_of_pocketInputsBelow
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_pocketInputsBelow
#audit_axioms GroupApproximation.GGT.VanKampen.OsinMultipleEdgeCutSectionStatement.toBelow
#audit_axioms GroupApproximation.GGT.VanKampen.osinSection97PocketInputsBelow_of_parts
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_pocketPartsBelow
