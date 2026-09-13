import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerSmallFaces
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonLabels
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketDiscMerge
import GroupApproximation.Meta.AxiomGuard

/-!
# C6′ through the disc region of the merged pocket

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`"; and the proof of Lemma 9.7(a): "otherwise one can include the
ε-contiguity subdiagrams corresponding to the edges `e` and `f` of `Φ′_M` into a single
ε-contiguity subdiagram in the obvious way, contrary to the definition of `M`."

`TwoGonHoldsInput` (C6′, `Estimating/OsinAppendixEulerSmallFaces.lean`) says that a two-gon of
`phiMapO` with no corner in its gap that holds no relator cell gives a contradiction.  The labels
of the two-gon are exterior regions `a ≠ b` of one cell to one section (`exists_twoGonLabels`).
Their merged face set, `a`, the pocket between them and `b`, is bounded by a reversed arc of the
cell, the right side of `a`, an arc of the boundary and the left side of `b`.

That face set is a disc, but when the two outer sides touch at a vertex its complement is not:
the complement splits into the exterior side and a lake holding the cell.  So no `PocketRegion`
has it as faces, and `EmptyTwoGonInput` cannot fire on it.  The collapse of
`GloballyDistinguishedSectionFamily.false_of_disc_collapse_singleton` needs only the inner disc
region (`Surgery.InnerDiscRegion`).  This module asks for exactly that.

* `GloballyDistinguishedSectionFamily.false_of_mergeDisc`: a disc region of G-cells whose cycle,
  started at some dart, reads the decomposition, and which every other selected region avoids, gives
  a contradiction.  This is the argument of `emptyTwoGonInput_holds` without the complement.
* `TwoGonMergeDiscInput`: for the labels of a two-gon, such a disc region with the printed arc
  bounds.
* `twoGonHoldsInput_of_mergeDisc`: `TwoGonHoldsInput` from `TwoGonMergeDiscInput`.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.7(a)); certifies no printed sentence on its
own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The merged pocket refutes the choice of the family.**  Let `a ≠ b` be exterior regions of
the cell `i` to the section `j`, and `R` a disc region of G-cells whose cycle, started at some
dart, is a reversed arc of the cell, the right side of `a`, an arc of the boundary and the left side
of `b`.  If every other selected region avoids `R`, the source arc spans the source arcs of `a` and
`b`, and the target arc runs from the start of the target arc of `a` to the end of that of `b`, then
the collapse of `R` merges `a` and `b` into one contiguity region, against the choice of the
family. -/
theorem GloballyDistinguishedSectionFamily.false_of_mergeDisc
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ RegionCandidate.exteriorAt S.family i)
    (hb : b ∈ RegionCandidate.exteriorAt S.family i) (hab : a ≠ b)
    (hja : RegionCandidate.TargetsSectionIndex cuts j a)
    (hjb : RegionCandidate.TargetsSectionIndex cuts j b)
    (R : Surgery.InnerDiscRegion S.diagram)
    (source : CyclicArc (cellDarts S.diagram i))
    (target : CyclicArc (targetDarts S.diagram none)) {k : ℕ}
    (hdecomp : R.region.cycle.rotate k =
      source.reverseDarts ++ a.2.rightSide ++ target.darts ++ b.2.leftSide)
    (hothers : ∀ x ∈ S.family, x ≠ a → x ≠ b → Disjoint x.1 R.faces)
    (hsource : a.2.sourceArc.length + b.2.sourceArc.length ≤ source.length)
    (hstart : target.start.1 = a.2.targetArc.start.1)
    (hend : target.start.1 + target.length = b.2.targetArc.start.1 + b.2.targetArc.length)
    (htarget : a.2.targetArc.length + b.2.targetArc.length ≤ target.length) : False := by
  classical
  obtain ⟨_, hja1, _⟩ := hja
  obtain ⟨_, _, hjb2⟩ := hjb
  have hrot : R.region.cycle.rotate k =
      source.reverseDarts ++ a.2.rightSide ++ targetBoundaryDarts S.diagram none target ++
        b.2.leftSide :=
    hdecomp
  have hright := a.2.rightSide_length_le
  have hleft := b.2.leftSide_length_le
  have hrightNorm := a.2.rightSide_norm_le
  have hleftNorm := b.2.leftSide_norm_le
  let H := R.mergedGeometry source target hrot hright hleft hrightNorm hleftNorm
  have hHsource : H.sourceArc.length = source.length :=
    R.mergedGeometry_sourceArc_length source target hrot hright hleft hrightNorm hleftNorm
  have hHtarget : H.targetArc.length = target.length :=
    R.mergedGeometry_targetArc_length source target hrot hright hleft hrightNorm hleftNorm
  have hHstart : H.targetArc.start.1 = target.start.1 :=
    R.mergedGeometry_targetArc_start source target hrot hright hleft hrightNorm hleftNorm
  have hmem : ∀ x ∈ RegionCandidate.exteriorAt S.family i, x ∈ S.family := fun _ hx =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hsub : ({a, b} : Finset (RegionCandidate D eps S.diagram)) ⊆ S.family :=
    Finset.insert_subset_iff.mpr ⟨hmem a ha, Finset.singleton_subset_iff.mpr (hmem b hb)⟩
  have hcard : 2 ≤ ({a, b} : Finset (RegionCandidate D eps S.diagram)).card :=
    (Finset.card_pair_eq_two_iff.mpr hab).ge
  have havoid : ∀ x ∈ S.family, x ∉ ({a, b} : Finset (RegionCandidate D eps S.diagram)) →
      Disjoint x.1 R.faces := fun x hx hxab =>
    hothers x hx (fun h => hxab (by simp [h])) (fun h => hxab (by simp [h]))
  have hrespects : RegionCandidate.RespectsSections cuts
      (⟨{R.merged}, H⟩ : RegionCandidate D eps R.diagram) := by
    refine ⟨fun h => Option.some_ne_none _ h.symm, fun _ => ⟨j, rfl, ?_, ?_⟩⟩
    · show cuts.cut j.castSucc ≤ H.targetArc.start.1
      omega
    · show H.targetArc.start.1 + H.targetArc.length ≤ cuts.cut j.succ
      omega
  obtain ⟨has, hat⟩ := S.nondegenerate a (hmem a ha)
  have hHs : 0 < H.sourceArc.length := by omega
  have hHt : 0 < H.targetArc.length := by omega
  have hweight : EstimatingSelection.familyWeight RegionCandidate.weight
      ({a, b} : Finset (RegionCandidate D eps S.diagram)) ≤
        H.sourceArc.length + H.targetArc.length := by
    unfold EstimatingSelection.familyWeight
    rw [Finset.sum_pair hab, hHsource, hHtarget]
    simp only [RegionCandidate.weight]
    omega
  exact S.false_of_disc_collapse_singleton R {a, b} hsub hcard havoid H hrespects hHs hHt
    hweight

/-- **The merge disc of a two-gon of `Φ'_M`**, the geometric content of C6′ that survives a lake.
Take the binders of `TwoGonHoldsInput` and the labels of the two-gon given by
`exists_twoGonLabels`: exterior regions `a ≠ b` of the cell `i`, both targeting the section `j`,
with the target arc of `a` ending before that of `b` starts.  Then there are a disc region `R` of
G-cells, a source arc on the cell `i`, a target arc on the oriented outer boundary and a rotation `k`
such that the cycle of `R` rotated by `k` is `source.reverseDarts ++ a.rightSide ++ target.darts ++
b.leftSide`, every other selected region avoids `R`, the source arc is at least as long as the
source arcs of `a` and `b` together, and the target arc runs from the start of the target arc of `a`
to the end of that of `b`. -/
def TwoGonMergeDiscInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
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
                          ∃ (R : Surgery.InnerDiscRegion S.diagram)
                            (source : CyclicArc (cellDarts S.diagram i))
                            (target : CyclicArc (targetDarts S.diagram none)) (k : ℕ),
                            R.region.cycle.rotate k =
                                source.reverseDarts ++ a.2.rightSide ++ target.darts ++
                                  b.2.leftSide ∧
                              (∀ x ∈ S.family, x ≠ a → x ≠ b → Disjoint x.1 R.faces) ∧
                              a.2.sourceArc.length + b.2.sourceArc.length ≤ source.length ∧
                              target.start.1 = a.2.targetArc.start.1 ∧
                              target.start.1 + target.length =
                                b.2.targetArc.start.1 + b.2.targetArc.length ∧
                              a.2.targetArc.length + b.2.targetArc.length ≤ target.length

/-- **C6′ from the merge disc.**  The labels of the two-gon give exterior regions `a ≠ b` of one
cell to one section, and `TwoGonMergeDiscInput` gives their merge disc, which
`GloballyDistinguishedSectionFamily.false_of_mergeDisc` refutes. -/
theorem twoGonHoldsInput_of_mergeDisc {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (hdisc : TwoGonMergeDiscInput.{u, w, v} D lambda c eps W) :
    TwoGonHoldsInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell
  obtain ⟨y, -, -, -, -, j, hya, hyb, hab, hja, hjb, horder⟩ :=
    RegionCandidate.exists_twoGonLabels S hmulti P hf hcorner
  obtain ⟨R, source, target, k, hdecomp, hothers, hsource, hstart, hend, htarget⟩ :=
    hdisc Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell _ j _ hya _ hyb hab
      hja hjb horder
  exact S.false_of_mergeDisc hya hyb hab hja hjb R source target hdecomp hothers hsource hstart
    hend htarget

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.false_of_mergeDisc
#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonMergeDiscInput
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonHoldsInput_of_mergeDisc
