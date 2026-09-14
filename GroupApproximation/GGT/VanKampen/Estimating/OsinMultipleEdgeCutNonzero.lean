import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionSections
import GroupApproximation.Meta.AxiomGuard

/-!
# The multiple-edge cut with transports for regions of nonzero degree

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(a): the subdiagram `Ξ` between two distinguished
`ε`-contiguity subdiagrams joining the same two cells, with `∂Ξ = s_1 t_1 s_2 t_2`.

`OsinMultipleEdgeCut` transports every region of an O-equivalent copy of `Ξ` to `t_1` or `t_2` into
a cell-to-cell region of an O-equivalent copy of `Δ`.  The component-route transports of lane
w1-binder-6 glue a copy of the pocket without following cycles and keep the exterior component.  They
need a nonempty source arc: a region with both arcs empty is joined to nothing, and it can sit on a
component that is dropped.  Osin's contradiction only bounds degrees from above, and a region of
degree `0` meets those bounds at once, so transports of the regions of nonzero degree suffice.

* `OsinMultipleEdgeCutNonzero`: `OsinMultipleEdgeCut` with the transport asked only for regions with
  a nonempty source arc; `OsinMultipleEdgeCut.toNonzero`.
* `OsinMultipleEdgeCutNonzero.false_of_below`: Osin's contradiction, as
  `OsinMultipleEdgeCut.false_of_below`.
* `OsinMultipleEdgeCutNonzero.ofPocketRegion`: the cut from a pocket region, as
  `OsinMultipleEdgeCut.ofPocketRegion`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(a));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

/-- **The multiple-edge cut, with transports for regions of nonzero degree**: `OsinMultipleEdgeCut`
whose transport is asked only for regions with a nonempty source arc. -/
structure OsinMultipleEdgeCutNonzero {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W) where
  enclosed : DiscDiagram.{u, w, v} W
  leastArea : enclosed.LeastArea
  rCellCount_pos : 0 < enclosed.rCellCount
  rCellCount_lt : enclosed.rCellCount < Delta.rCellCount
  sections : SectionCuts D lambda c enclosed.boundaryWord
  count_eq : sections.count = 4
  side_short : ∀ j : Fin sections.count, ((j : ℕ) = 0 ∨ (j : ℕ) = 2) →
    sections.cut j.succ - sections.cut j.castSucc ≤ eps
  transport : ∀ j : Fin sections.count, ((j : ℕ) = 1 ∨ (j : ℕ) = 3) →
    ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram enclosed Xi →
      ∀ a : RegionCandidate D eps Xi,
        RegionCandidate.TargetsSectionIndex sections j a → a.2.sourceArc.length ≠ 0 →
          ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y)
            (t : Fin Y.rCellCount),
            Nonempty (OEquivalentDiscDiagram Delta Y) ∧
              b.2.target = some t ∧ b.2.source ≠ t ∧
              b.contiguityDegree = a.contiguityDegree

/-- A multiple-edge cut is one with transports for regions of nonzero degree. -/
def OsinMultipleEdgeCut.toNonzero {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} (cut : OsinMultipleEdgeCut D lambda c eps Delta) :
    OsinMultipleEdgeCutNonzero D lambda c eps Delta where
  enclosed := cut.enclosed
  leastArea := cut.leastArea
  rCellCount_pos := cut.rCellCount_pos
  rCellCount_lt := cut.rCellCount_lt
  sections := cut.sections
  count_eq := cut.count_eq
  side_short := cut.side_short
  transport := fun j hj Xi E a ha _ => cut.transport j hj Xi E a ha

/-- **Osin's contradiction, over transports for regions of nonzero degree**: as
`OsinMultipleEdgeCut.false_of_below`.  A region of degree `0` to `t_1` or `t_2` is below `μ`
without a transport. -/
theorem OsinMultipleEdgeCutNonzero.false_of_below
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps rho : ℕ}
    {Delta : DiscDiagram.{u, w, v} W}
    (cut : OsinMultipleEdgeCutNonzero D lambda c eps Delta)
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    (hlea : Delta.LeastArea)
    (hb : ∃ T : RealizedSectionFamily D lambda c eps cut.enclosed
        cut.sections, OsinLemma97bConclusion mu T) :
    False := by
  obtain ⟨T, _source, present, region, _hsource, htargets, _hdisjoint, hsum⟩ := hb
  have hboundary : T.diagram.boundaryWord = cut.enclosed.boundaryWord :=
    T.equiv.boundaryWord_eq
  have hbound : ∀ j ∈ present, (region j).contiguityDegree ≤
      (if (j : ℕ) = 0 ∨ (j : ℕ) = 2 then mu / 2 else mu) := by
    intro j hj
    have hj4 : (j : ℕ) < 4 := by
      have hlt := j.isLt
      have hc := cut.count_eq
      omega
    by_cases hside : (j : ℕ) = 0 ∨ (j : ℕ) = 2
    · rw [if_pos hside]
      exact le_of_lt (RegionCandidate.contiguityDegree_lt_half_mu_of_shortSection
        hcondition hlambda hmu hrho hlarge cut.sections hboundary
        (cut.side_short j hside) (region j) (htargets j hj))
    · rw [if_neg hside]
      have hcell : (j : ℕ) = 1 ∨ (j : ℕ) = 3 := by omega
      by_cases h0 : (region j).2.sourceArc.length = 0
      · have hdeg0 : (region j).contiguityDegree = 0 := by
          unfold RegionCandidate.contiguityDegree
          rw [h0, Nat.cast_zero, zero_div]
        rw [hdeg0]
        exact hmu.le
      · obtain ⟨Y, b, t, ⟨EY⟩, htarget, hne, hdeg⟩ :=
          cut.transport j hcell T.diagram T.equiv (region j) (htargets j hj) h0
        rw [← hdeg]
        exact le_of_lt (RegionCandidate.contiguityDegree_lt_mu_of_o52 hO52 hcondition hlambda hmu
          hrho hlarge (EY.leastArea hlea) b htarget hne)
  have hle := Finset.sum_le_sum hbound
  have htotal : (∑ j ∈ present, (if (j : ℕ) = 0 ∨ (j : ℕ) = 2 then mu / 2 else mu)) ≤
      ∑ j : Fin cut.sections.count, (if (j : ℕ) = 0 ∨ (j : ℕ) = 2 then mu / 2 else mu) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ present)
    intro j _ _
    split_ifs <;> linarith
  have hfour : (∑ j : Fin cut.sections.count,
      (if (j : ℕ) = 0 ∨ (j : ℕ) = 2 then mu / 2 else mu)) = 3 * mu := by
    have hc := cut.count_eq
    revert hc
    generalize cut.sections.count = n
    intro hn
    subst hn
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
    norm_num
    ring
  linarith

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

/-- **The multiple-edge cut from a pocket region, with transports for regions of nonzero degree**: as
`OsinMultipleEdgeCut.ofPocketRegion`. -/
noncomputable def OsinMultipleEdgeCutNonzero.ofPocketRegion {D : RelGenSet G Lambda}
    {lambda c : ℝ} {eps : ℕ} {Delta Delta' : DiscDiagram.{u, w, v} W}
    (equiv : OEquivalentDiscDiagram Delta Delta') (hlea : Delta.LeastArea)
    (P : PocketRegion Delta')
    {C C' : RelatorCell Delta'.toCombMap Delta'.outerFace W}
    (hC : C ∈ Delta'.relatorCells) (hCf : C.face ∈ P.faces)
    (hC' : C' ∈ Delta'.relatorCells) (hC'f : C'.face ∉ P.faces)
    (s₁ t₁ s₂ t₂ : List Delta'.toCombMap.Dart)
    (hdecomposition : Embedded.invDarts Delta' P.outer.cycle = s₁ ++ t₁ ++ s₂ ++ t₂)
    (hquasi : ∀ part ∈ [s₁, t₁, s₂, t₂],
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta' part))
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps)
    (htransport :
      ∀ j : Fin (P.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).count,
        ((j : ℕ) = 1 ∨ (j : ℕ) = 3) →
          ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram P.diagram Xi →
            ∀ a : RegionCandidate D eps Xi,
              RegionCandidate.TargetsSectionIndex
                  (P.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi) j a →
                a.2.sourceArc.length ≠ 0 →
                  ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y)
                    (t : Fin Y.rCellCount),
                    Nonempty (OEquivalentDiscDiagram Delta' Y) ∧
                      b.2.target = some t ∧ b.2.source ≠ t ∧
                      b.contiguityDegree = a.contiguityDegree) :
    OsinMultipleEdgeCutNonzero D lambda c eps Delta :=
  have key := P.fourSectionCuts_leastAreaCut D lambda c eps (equiv.leastArea hlea) hC hCf hC'
    hC'f s₁ t₁ s₂ t₂ hdecomposition hquasi hs₁ hs₂
  { enclosed := P.diagram
    leastArea := key.1
    rCellCount_pos := key.2.1
    rCellCount_lt := lt_of_lt_of_eq key.2.2.1 equiv.rCellCount_eq
    sections := P.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi
    count_eq := key.2.2.2.1
    side_short := key.2.2.2.2
    transport := by
      intro j hj Xi E a ha h0
      obtain ⟨Y, b, t, ⟨EY⟩, htarget, hne, hdeg⟩ := htransport j hj Xi E a ha h0
      exact ⟨Y, b, t, ⟨equiv.trans EY⟩, htarget, hne, hdeg⟩ }

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinMultipleEdgeCut.toNonzero
#audit_axioms GroupApproximation.GGT.VanKampen.OsinMultipleEdgeCutNonzero.false_of_below
#audit_axioms GroupApproximation.GGT.VanKampen.OsinMultipleEdgeCutNonzero.ofPocketRegion
