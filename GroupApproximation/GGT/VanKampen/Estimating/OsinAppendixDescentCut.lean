import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixAssemblyPocket
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionInduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.7(b): the section pocket as a named cut

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` (quoted in `OsinAppendixAssemblyPocket`).  Two distinct
exterior regions of one cell `Π` to one section `q_j` of a distinguished system bound
such a pocket: `s_1, s_2` are their side arcs, `t_1` lies on `∂Π`, and `t_2` lies in
`q_j`.

## What is proved here

* `OsinSectionPocketCut`: the pocket at the section `q_j`.  It extends
  `OsinExteriorDoubleCut` by the transport of the regions to `t_2` to regions of an
  O-equivalent copy of `Δ` to `q_j`, with the same degree;
* `SectionPocketCutInput`: the producer of the pocket, the single geometric input
  of the descent;
* `OsinLemma97Below.mono`;
* `OsinExteriorDoubleCut.contiguityDegree_lt_half_mu_of_side` and
  `OsinExteriorDoubleCut.contiguityDegree_lt_mu_of_section_one`: the degree bounds
  at `s_1, s_2` (below `μ/2`) and at `t_1` (below `μ`, O52 after gluing), in every
  O-equivalent copy of the pocket;
* `false_of_osinLemma97bConclusion_of_degree_lt`: clause (b) is impossible at a
  four-section diagram whose sections carry the degree bounds `μ/2, μ, μ/2, μ`,
  since `3μ ≤ 1 − 13μ`;
* `OsinSectionPocketCut.false_of_inner`: a pocket inside a pocket at `s_1`, `t_1`
  or `s_2` contradicts clause (b) at the inner pocket;
* `osinLemma97bConclusion_of_region`: one region to a section of degree above
  `1 − 13μ`, in an O-equivalent copy, is clause (b).
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w}

/-! ## The pocket at a section -/

/-- **The pocket between two exterior regions of one cell to one section** (Osin's
`Γ_1`, at the section `q_j`).  The fields of `OsinExteriorDoubleCut`: a least-area
subdiagram with at least one and fewer relator cells than `Δ`, four sections
`s_1 t_1 s_2 t_2`, the side arcs `s_1, s_2` of length at most `ε`, and the regions to
`t_1` transported to cell-to-cell regions of an O-equivalent copy of `Δ`.  In
addition, the regions to `t_2` are transported to regions of an O-equivalent copy of
`Δ` to the section `q_j`, with the same contiguity degree. -/
structure OsinSectionPocketCut {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord) (j : Fin cuts.count)
    extends OsinExteriorDoubleCut D lambda c eps Delta where
  sectionTransport : ∀ k : Fin sections.count, (k : ℕ) = 3 →
    ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram enclosed Xi →
      ∀ a : RegionCandidate D eps Xi,
        RegionCandidate.TargetsSectionIndex sections k a →
          ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y),
            Nonempty (OEquivalentDiscDiagram Delta Y) ∧
              RegionCandidate.TargetsSectionIndex cuts j b ∧
              b.contiguityDegree = a.contiguityDegree

/-- **The pocket producer**, the geometric input of the descent: two distinct
exterior regions of one cell of a distinguished system to one section bound a
pocket.  A pocket without relator cells is excluded by merging the two regions,
against the extremality of the system. -/
def SectionPocketCutInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        ∀ (i : Fin S.diagram.rCellCount) (j : Fin cuts.count),
          ∀ a ∈ RegionCandidate.exteriorAt S.family i,
            ∀ b ∈ RegionCandidate.exteriorAt S.family i, a ≠ b →
              RegionCandidate.TargetsSectionIndex cuts j a →
                RegionCandidate.TargetsSectionIndex cuts j b →
                  Nonempty (OsinSectionPocketCut D lambda c eps Delta cuts j)

/-! ## The inductive assumption -/

/-- Clause (b) below `n` gives clause (b) below every `m ≤ n`. -/
theorem OsinLemma97Below.mono {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c mu : ℝ} {eps : ℕ} {m n : ℕ}
    (hbelow : OsinLemma97Below.{u, w, v} D lambda c mu eps W n) (hmn : m ≤ n) :
    OsinLemma97Below.{u, w, v} D lambda c mu eps W m := by
  intro Xi cutsXi hlea hpos hlt
  exact hbelow Xi cutsXi hlea hpos (lt_of_lt_of_le hlt hmn)

/-! ## Degree bounds in the copies of a pocket -/

/-- **The side arcs**: a region to `s_1` or `s_2` in any O-equivalent copy of the
pocket has degree below `μ/2`. -/
theorem OsinExteriorDoubleCut.contiguityDegree_lt_half_mu_of_side
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps rho : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (cut : OsinExteriorDoubleCut D lambda c eps Delta)
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hmu : 0 < mu) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    (k : Fin cut.sections.count) (hk : (k : ℕ) = 0 ∨ (k : ℕ) = 2)
    {X : DiscDiagram.{u, w, v} W} (EX : OEquivalentDiscDiagram cut.enclosed X)
    (a : RegionCandidate D eps X)
    (ha : RegionCandidate.TargetsSectionIndex cut.sections k a) :
    a.contiguityDegree < mu / 2 :=
  RegionCandidate.contiguityDegree_lt_half_mu_of_shortSection hcondition hlambda hmu hrho
    hlarge cut.sections EX.boundaryWord_eq (cut.side_short k hk) a ha

/-- **The arc of the cell**: a region to `t_1` in any O-equivalent copy of the pocket
has degree below `μ`, by O52 at the glued copy of `Δ`. -/
theorem OsinExteriorDoubleCut.contiguityDegree_lt_mu_of_section_one
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps rho : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (cut : OsinExteriorDoubleCut D lambda c eps Delta)
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hmu : 0 < mu) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    (hlea : Delta.LeastArea)
    (k : Fin cut.sections.count) (hk : (k : ℕ) = 1)
    {X : DiscDiagram.{u, w, v} W} (EX : OEquivalentDiscDiagram cut.enclosed X)
    (a : RegionCandidate D eps X)
    (ha : RegionCandidate.TargetsSectionIndex cut.sections k a) :
    a.contiguityDegree < mu := by
  obtain ⟨Y, b, t, ⟨EY⟩, htarget, hne, hdeg⟩ := cut.cellTransport k hk X EX a ha
  rw [← hdeg]
  exact RegionCandidate.contiguityDegree_lt_mu_of_o52 hO52 hcondition hlambda hmu hrho
    hlarge (EY.leastArea hlea) b htarget hne

/-! ## The contradiction at a pocket -/

/-- **Osin's contradiction, from degree bounds.**  At a four-section diagram in every
O-equivalent copy of which the regions to the sections have degrees below
`μ/2, μ, μ/2, μ`, clause (b) is impossible: the selected degrees total at most `3μ`,
and `3μ ≤ 1 − 13μ` for `μ ≤ 1/16`. -/
theorem false_of_osinLemma97bConclusion_of_degree_lt
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps : ℕ} {Xi : DiscDiagram.{u, w, v} W}
    {sections : SectionCuts D lambda c Xi.boundaryWord}
    (hcount : sections.count = 4) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16)
    (hdegree : ∀ k : Fin sections.count, ∀ (X : DiscDiagram.{u, w, v} W),
      OEquivalentDiscDiagram Xi X → ∀ a : RegionCandidate D eps X,
        RegionCandidate.TargetsSectionIndex sections k a →
          a.contiguityDegree < (if (k : ℕ) = 0 ∨ (k : ℕ) = 2 then mu / 2 else mu))
    (hb : ∃ T : RealizedSectionFamily D lambda c eps Xi sections,
      OsinLemma97bConclusion mu T) :
    False := by
  obtain ⟨T, _source, present, region, _hsource, htargets, _hdisjoint, hsum⟩ := hb
  have hbound : ∀ j ∈ present, (region j).contiguityDegree ≤
      (if (j : ℕ) = 0 ∨ (j : ℕ) = 2 then mu / 2 else mu) := fun j hj =>
    le_of_lt (hdegree j T.diagram T.equiv (region j) (htargets j hj))
  have hle := Finset.sum_le_sum hbound
  have htotal : (∑ j ∈ present, (if (j : ℕ) = 0 ∨ (j : ℕ) = 2 then mu / 2 else mu)) ≤
      ∑ j : Fin sections.count, (if (j : ℕ) = 0 ∨ (j : ℕ) = 2 then mu / 2 else mu) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ present)
    intro j _ _
    split_ifs <;> linarith
  have hfour : (∑ j : Fin sections.count,
      (if (j : ℕ) = 0 ∨ (j : ℕ) = 2 then mu / 2 else mu)) = 3 * mu := by
    have hc := hcount
    revert hc
    generalize sections.count = n
    intro hn
    subst hn
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
    norm_num
    ring
  linarith

/-- **A pocket inside a pocket, at `s_1`, `t_1` or `s_2`, contradicts clause (b) at
the inner pocket.**  Its sides give `μ/2`, its arc on the inner cell gives `μ` (O52 in
a copy of the outer pocket), and its fourth section lies in a section of the outer
pocket other than `t_2`: `μ/2` at a side arc, `μ` at `t_1` (O52 in a copy of `Δ`). -/
theorem OsinSectionPocketCut.false_of_inner
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps rho : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord} {j : Fin cuts.count}
    (cut : OsinSectionPocketCut D lambda c eps Delta cuts j)
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    (hlea : Delta.LeastArea)
    (k : Fin cut.sections.count) (hk : (k : ℕ) ≠ 3)
    (inner : OsinSectionPocketCut D lambda c eps cut.enclosed cut.sections k)
    (hb : ∃ T : RealizedSectionFamily D lambda c eps inner.enclosed inner.sections,
      OsinLemma97bConclusion mu T) :
    False := by
  refine false_of_osinLemma97bConclusion_of_degree_lt inner.count_eq hmu hmuUpper ?_ hb
  intro k' X EX a ha
  by_cases hside : (k' : ℕ) = 0 ∨ (k' : ℕ) = 2
  · rw [if_pos hside]
    exact inner.toOsinExteriorDoubleCut.contiguityDegree_lt_half_mu_of_side hcondition
      hlambda hmu hrho hlarge k' hside EX a ha
  · rw [if_neg hside]
    by_cases h1 : (k' : ℕ) = 1
    · exact inner.toOsinExteriorDoubleCut.contiguityDegree_lt_mu_of_section_one hO52
        hcondition hlambda hmu hrho hlarge cut.leastArea k' h1 EX a ha
    · have h3 : (k' : ℕ) = 3 := by
        have hlt := k'.isLt
        have hc := inner.count_eq
        omega
      obtain ⟨Y, b, ⟨EY⟩, hbY, hdeg⟩ := inner.sectionTransport k' h3 X EX a ha
      rw [← hdeg]
      by_cases hside' : (k : ℕ) = 0 ∨ (k : ℕ) = 2
      · have hhalf := cut.toOsinExteriorDoubleCut.contiguityDegree_lt_half_mu_of_side
          hcondition hlambda hmu hrho hlarge k hside' EY b hbY
        linarith
      · have h1' : (k : ℕ) = 1 := by
          have hlt := k.isLt
          have hc := cut.count_eq
          omega
        exact cut.toOsinExteriorDoubleCut.contiguityDegree_lt_mu_of_section_one hO52
          hcondition hlambda hmu hrho hlarge hlea k h1' EY b hbY

/-! ## One large region is clause (b) -/

/-- The empty section family on an O-equivalent copy of a least-area diagram. -/
def RealizedSectionFamily.emptyOfLeastArea {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (cuts : SectionCuts D lambda c Delta.boundaryWord) {Y : DiscDiagram.{u, w, v} W}
    (EY : OEquivalentDiscDiagram Delta Y) (hlea : Delta.LeastArea) :
    RealizedSectionFamily D lambda c eps Delta cuts where
  diagram := Y
  equiv := EY
  reduced := DiscDiagram.reduced_of_leastArea (EY.leastArea hlea)
  family := ∅
  pairwise := by
    intro a ha
    simp at ha
  respects := by
    intro a ha
    simp at ha
  nondegenerate := by
    intro a ha
    simp at ha

/-- **One large region is clause (b).**  A region to the section `q_j` of degree above
`1 − 13μ` in an O-equivalent copy of `Δ` is a selection with one present section. -/
theorem osinLemma97bConclusion_of_region {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c mu : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord} (hlea : Delta.LeastArea)
    {Y : DiscDiagram.{u, w, v} W} (EY : OEquivalentDiscDiagram Delta Y) (j : Fin cuts.count)
    (b : RegionCandidate D eps Y) (hb : RegionCandidate.TargetsSectionIndex cuts j b)
    (hdeg : 1 - 13 * mu < b.contiguityDegree) :
    ∃ T : RealizedSectionFamily D lambda c eps Delta cuts, OsinLemma97bConclusion mu T := by
  refine ⟨RealizedSectionFamily.emptyOfLeastArea (eps := eps) cuts EY hlea, b.2.source,
    {j}, fun _ => b, ?_, ?_, ?_, ?_⟩
  · intro k _
    rfl
  · intro k hk
    rw [Finset.mem_singleton] at hk
    subst hk
    exact hb
  · intro k hk l hl hkl
    rw [Finset.mem_singleton] at hk hl
    exact absurd (hk.trans hl.symm) hkl
  · rw [Finset.sum_singleton]
    exact hdeg

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinSectionPocketCut
#audit_axioms GroupApproximation.GGT.VanKampen.SectionPocketCutInput
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma97Below.mono
#audit_axioms GroupApproximation.GGT.VanKampen.OsinExteriorDoubleCut.contiguityDegree_lt_half_mu_of_side
#audit_axioms GroupApproximation.GGT.VanKampen.OsinExteriorDoubleCut.contiguityDegree_lt_mu_of_section_one
#audit_axioms GroupApproximation.GGT.VanKampen.false_of_osinLemma97bConclusion_of_degree_lt
#audit_axioms GroupApproximation.GGT.VanKampen.OsinSectionPocketCut.false_of_inner
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.emptyOfLeastArea
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma97bConclusion_of_region
