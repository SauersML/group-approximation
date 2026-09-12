import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixDescentCut
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixAssemblyDescent
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.7(b): the descent through section pockets

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b).  At the cell `Π` of Corollary 9.6,
if two exterior regions of `Π` go to one section `q_j`, they bound the pocket `Γ_1`
with `∂Γ_1 = s_1 t_1 s_2 t_2`.  Corollary 9.6 at `Γ_1` gives a cell above `1 − 11μ`
(40); a second region of that cell to `s_1`, `t_1` or `s_2` would bound an inner
pocket contradicting the inductive assumption, so the regions to `t_2` total above
`1 − 13μ`.  Either one region to `t_2` carries it, and transports to `q_j`, or two
regions to `t_2` bound a smaller pocket, and the argument repeats.

## What is proved here

* `exists_elevenCell_of_below`: Corollary 9.6 at a least-area diagram from the
  inductive assumption below its number of relator cells, with `(∗)`;
* `OsinSectionPocketCut.exists_large_region`: every section pocket gives a region of
  an O-equivalent copy of `Δ` to `q_j` of degree above `1 − 13μ`, by induction on the
  number of relator cells of the pocket;
* `descentInput_of_sectionPocketCut`: `DescentInput` from `SectionPocketCutInput`
  and the inputs of `osinLemma97_atParameters_of_inputs`.

The inductive assumption is used at pockets only through clause (b) below `n`, with
a fresh distinguished system at each pocket, so no extremality is transported.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w}

/-! ## Corollary 9.6 below the inductive bound -/

/-- **Corollary 9.6 from the inductive assumption.**  At a least-area diagram with a
relator cell, clause (b) below its number of relator cells gives `(∗)` and a
distinguished system with a cell whose exterior regions total above `1 − 11μ`. -/
theorem exists_elevenCell_of_below
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps rho : ℕ}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    (hthreshold : 1 ≤ mu * Real.sqrt (rho : ℝ))
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (hmulti : MultipleEdgeCutInput.{u, w, v} D lambda c eps W)
    (hloop : LoopCutInput.{u, w, v} D lambda c eps W)
    (heuler : EulerCountInput.{u, w, v} D lambda c eps W)
    (h94 : UnboundInput.{u, w, v} D lambda c eps rho W)
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
      obtain ⟨cut⟩ := hmulti Delta cuts hlea S a ha b hb hab i j hai hbj
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
  have hunbound94 := h94 Delta cuts hlea hcells S hcard
  have hunbound := RegionCandidate.unbound_total_lt_mu S.family
    (fun i => hcondition.long _ (cell S.diagram i).word_mem) hmu.le
    (by rw [← hcountEq] at hunbound94; exact hunbound94) hthreshold
  obtain ⟨i, hi⟩ := RegionCandidate.exists_large_exterior_collection S.family
    S.pairwise hinterior hunbound
  exact ⟨S, hloopsS, hmultiS, i, hi⟩

/-! ## The descent through pockets -/

/-- **Every section pocket carries a large region to its section.**  Below the
inductive bound `n`, a pocket at the section `q_j` of a least-area diagram `Δ` gives a
region of an O-equivalent copy of `Δ` to `q_j` of degree above `1 − 13μ`.

By induction on the number of relator cells of the pocket: Corollary 9.6 at the
pocket gives a cell above `1 − 11μ`; two of its regions to `s_1`, `t_1` or `s_2` would
bound an inner pocket against clause (b) below `n`
(`OsinSectionPocketCut.false_of_inner`), so its regions to `t_2` total above
`1 − 13μ` (`OsinExteriorDoubleCut.lastSection_total_gt`).  One region to `t_2` has
degree above `1 − 13μ` and transports to `q_j`; two regions to `t_2` bound a smaller
pocket, whose large region transports to `q_j`. -/
theorem OsinSectionPocketCut.exists_large_region
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps rho : ℕ}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    (hthreshold : 1 ≤ mu * Real.sqrt (rho : ℝ))
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (hmulti : MultipleEdgeCutInput.{u, w, v} D lambda c eps W)
    (hloop : LoopCutInput.{u, w, v} D lambda c eps W)
    (heuler : EulerCountInput.{u, w, v} D lambda c eps W)
    (h94 : UnboundInput.{u, w, v} D lambda c eps rho W)
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
      -- Corollary 9.6 at the pocket.
      have hbelowCut : OsinLemma97Below.{u, w, v} D lambda c mu eps W
          cut.enclosed.rCellCount := hbelow.mono (by omega)
      obtain ⟨S, _hloopsS, _hmultiS, i, h11⟩ := exists_elevenCell_of_below hcondition hlambda
        hmu hmuUpper hrho hlarge hthreshold hO52 hmulti hloop heuler h94 cut.enclosed
        cut.sections cut.leastArea cut.rCellCount_pos hbelowCut
      -- At most one region of the cell to each of `s_1`, `t_1`, `s_2`.
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
      -- The regions to `t_2` total above `1 − 13μ`.
      obtain ⟨j3, hj3⟩ : ∃ j3 : Fin cut.sections.count, (j3 : ℕ) = 3 :=
        ⟨⟨3, by have hc := cut.count_eq; omega⟩, rfl⟩
      have h13 := cut.toOsinExteriorDoubleCut.lastSection_total_gt hO52 hcondition hlambda hmu
        hrho hlarge hlea S.toRealizedSectionFamily i h11 hunique j3 hj3
      have hpos : (0 : ℝ) < ((cell S.diagram i).word.length : ℝ) :=
        cellWord_length_pos hcondition.toIsSmallCancellation hrho i
      by_cases huniq3 : ∀ a ∈ RegionCandidate.exteriorAt S.family i,
          ∀ b ∈ RegionCandidate.exteriorAt S.family i,
            RegionCandidate.TargetsSectionIndex cut.sections j3 a →
              RegionCandidate.TargetsSectionIndex cut.sections j3 b → a = b
      · -- One region to `t_2`: its degree is above `1 − 13μ`.
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
      · -- Two regions to `t_2`: a smaller pocket.
        push_neg at huniq3
        obtain ⟨a, ha, b, hb, hta, htb, hab⟩ := huniq3
        obtain ⟨cut'⟩ := hpocket cut.enclosed cut.sections cut.leastArea S i j3 a ha b hb hab
          hta htb
        have hlt' := cut'.rCellCount_lt
        obtain ⟨Y', b', ⟨EY'⟩, hbY', hdeg'⟩ := ih cut'.enclosed.rCellCount (by omega)
          cut.enclosed cut.sections j3 cut.leastArea cut' rfl (by omega)
        obtain ⟨Y, b'', hEY, hbY, hdegb⟩ := cut.sectionTransport j3 hj3 Y' EY' b' hbY'
        exact ⟨Y, b'', hEY, hbY, by rw [hdegb]; exact hdeg'⟩

/-! ## `DescentInput` from the pocket producer -/

/-- **`DescentInput` from the section pocket producer.**  At the cell of
Corollary 9.6, at most one exterior region per section gives clause (b) directly
(`osinLemma97bConclusion_of_exteriorUniqueAt`); two regions to one section bound a
pocket, whose large region to that section is clause (b)
(`osinLemma97bConclusion_of_region`). -/
theorem descentInput_of_sectionPocketCut
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps rho : ℕ}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    (hthreshold : 1 ≤ mu * Real.sqrt (rho : ℝ))
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (hmulti : MultipleEdgeCutInput.{u, w, v} D lambda c eps W)
    (hloop : LoopCutInput.{u, w, v} D lambda c eps W)
    (heuler : EulerCountInput.{u, w, v} D lambda c eps W)
    (h94 : UnboundInput.{u, w, v} D lambda c eps rho W)
    (hpocket : SectionPocketCutInput.{u, w, v} D lambda c eps W) :
    DescentInput.{u, w, v} D lambda c mu eps W := by
  rintro Delta cuts hlea _hcells hbelow S _hloopsS _hmultiS ⟨i, h11⟩
  by_cases huniq : S.toRealizedSectionFamily.ExteriorUniqueAt i
  · exact ⟨S.toRealizedSectionFamily,
      osinLemma97bConclusion_of_exteriorUniqueAt S.toRealizedSectionFamily i
        (RealizedSectionFamily.exteriorLarge_of_gt_eleven S.toRealizedSectionFamily i
          hmu.le h11)
        huniq hmuUpper (cellWord_length_pos hcondition.toIsSmallCancellation hrho i)⟩
  · unfold RealizedSectionFamily.ExteriorUniqueAt at huniq
    push_neg at huniq
    obtain ⟨j, a, ha, b, hb, hta, htb, hab⟩ := huniq
    obtain ⟨cut⟩ := hpocket Delta cuts hlea S i j a ha b hb hab hta htb
    obtain ⟨Y, r, ⟨EY⟩, hr, hdeg⟩ := OsinSectionPocketCut.exists_large_region hcondition
      hlambda hmu hmuUpper hrho hlarge hthreshold hO52 hmulti hloop heuler h94 hpocket hbelow
      cut.enclosed.rCellCount Delta cuts j hlea cut rfl cut.rCellCount_lt
    exact osinLemma97bConclusion_of_region hlea EY j r hr hdeg

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.exists_elevenCell_of_below
#audit_axioms GroupApproximation.GGT.VanKampen.OsinSectionPocketCut.exists_large_region
#audit_axioms GroupApproximation.GGT.VanKampen.descentInput_of_sectionPocketCut
