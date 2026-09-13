import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketDiscMerge
import GroupApproximation.Meta.AxiomGuard

/-!
# The zero-cell pocket merge

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(a): "otherwise one can include the
ε-contiguity subdiagrams corresponding to the edges `e` and `f` of `Φ'_M` into a single
ε-contiguity subdiagram in the obvious way, contrary to the definition of `M`."  Two selected
regions `a ≠ b` and a pocket region between them with no relator cell give one contiguity region.
If its arcs are nonempty and at least as long as the arcs of `a` and `b` together, the choice of
the distinguished system is contradicted.  The target of the merged region is a section, as in
Lemma 9.7(a), or a cell, as for a multiple edge in Lemma 9.7(b).

The pocket is collapsed through its disc region (`Surgery.InnerDiscRegion.ofPocketRegion`,
`Estimating/OsinPocketDiscMerge.lean`), so no boundary-walk hypothesis is needed and pinched
pockets are covered.

* `GloballyDistinguishedSectionFamily.false_of_disc_pair_singleton`: a collapsed disc region
  absorbing exactly two selected regions (`false_of_disc_collapse_singleton` with
  `absorbed = {a, b}`).
* `GloballyDistinguishedSectionFamily.false_of_zeroCellPocket`: the merged region read off a
  decomposition of the inverse complement cycle of the pocket.
* `ZeroCellPocketMergeStatement` and `zeroCellPocketMerge`: the merge over pocket-region data,
  proved.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace GloballyDistinguishedSectionFamily

variable {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **Two selected regions absorbed by one collapsed disc region.**  If the merged face of a
collapsed disc region is a contiguity region inside a section or to a cell, with nonempty arcs at
least as long as the arcs of two selected regions `a ≠ b` together, and every other selected
region avoids the collapsed faces, there is a contradiction. -/
theorem false_of_disc_pair_singleton
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {a b : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) (hb : b ∈ S.family)
    (hab : a ≠ b) (R : Surgery.InnerDiscRegion S.diagram)
    (havoid : ∀ x ∈ S.family, x ≠ a → x ≠ b → Disjoint x.1 R.faces)
    (H : ContiguityGeometry D eps R.diagram ({R.merged} : Finset R.diagram.toCombMap.Face))
    (hsection : H.target = none → ∃ j : Fin cuts.count,
      cuts.cut j.castSucc ≤ H.targetArc.start.1 ∧
        H.targetArc.start.1 + H.targetArc.length ≤ cuts.cut j.succ)
    (hsource : 0 < H.sourceArc.length) (htarget : 0 < H.targetArc.length)
    (hweight : a.weight + b.weight ≤ H.sourceArc.length + H.targetArc.length) : False := by
  classical
  refine S.false_of_disc_collapse_singleton R {a, b}
    (Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩)
    (Finset.card_pair_eq_two_iff.mpr hab).ge
    (fun x hx hxab => havoid x hx (fun h => hxab (by simp [h])) (fun h => hxab (by simp [h])))
    H ?_ hsource htarget ?_
  · intro hnone
    obtain ⟨j, hlo, hhi⟩ := hsection hnone
    exact ⟨j, hnone, hlo, hhi⟩
  · unfold EstimatingSelection.familyWeight
    rw [Finset.sum_pair hab]
    exact hweight

/-- **The zero-cell pocket merge, pocket form.**  Take two selected regions `a ≠ b` and a pocket
region with no relator cell, avoided by every other selected region.  Suppose its inverse
complement cycle is a reversed arc of a relator cell, a short side, an arc of the target and a
short side.  With the section condition, nonempty arcs and the weight bound, there is a
contradiction. -/
theorem false_of_zeroCellPocket
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {a b : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) (hb : b ∈ S.family)
    (hab : a ≠ b) (P : PocketRegion S.diagram)
    (hcells : ∀ C ∈ S.diagram.relatorCells, C.face ∉ P.faces)
    (havoid : ∀ x ∈ S.family, x ≠ a → x ≠ b → Disjoint x.1 P.faces)
    {source : Fin S.diagram.rCellCount} {target : Option (Fin S.diagram.rCellCount)}
    (sourceArc : CyclicArc (cellDarts S.diagram source))
    (targetArc : CyclicArc (targetDarts S.diagram target))
    {rightSide leftSide : List S.diagram.toCombMap.Dart}
    (hdecomp : invDarts S.diagram P.outer.cycle = sourceArc.reverseDarts ++ rightSide ++
      targetBoundaryDarts S.diagram target targetArc ++ leftSide)
    (hright : rightSide.length ≤ eps) (hleft : leftSide.length ≤ eps)
    (hrightNorm : WordMetric.wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord S.diagram rightSide)) ≤ eps)
    (hleftNorm : WordMetric.wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord S.diagram leftSide)) ≤ eps)
    (hsection : target = none → ∃ j : Fin cuts.count,
      cuts.cut j.castSucc ≤ targetArc.start.1 ∧
        targetArc.start.1 + targetArc.length ≤ cuts.cut j.succ)
    (hsource : 0 < sourceArc.length) (htarget : 0 < targetArc.length)
    (hweight : a.weight + b.weight ≤ sourceArc.length + targetArc.length) : False := by
  obtain ⟨k, hk⟩ := P.invDarts_outer_rotate
  have hrot : (Surgery.InnerDiscRegion.ofPocketRegion P hcells).region.cycle.rotate k =
      sourceArc.reverseDarts ++ rightSide ++ targetBoundaryDarts S.diagram target targetArc ++
        leftSide :=
    hk.symm.trans hdecomp
  refine S.false_of_disc_pair_singleton ha hb hab
    (Surgery.InnerDiscRegion.ofPocketRegion P hcells) havoid
    ((Surgery.InnerDiscRegion.ofPocketRegion P hcells).mergedGeometry sourceArc targetArc hrot
      hright hleft hrightNorm hleftNorm) ?_ ?_ ?_ ?_
  · rw [Surgery.InnerDiscRegion.mergedGeometry_targetArc_start,
      Surgery.InnerDiscRegion.mergedGeometry_targetArc_length,
      Surgery.InnerDiscRegion.mergedGeometry_target, Option.map_eq_none_iff]
    exact hsection
  · rw [Surgery.InnerDiscRegion.mergedGeometry_sourceArc_length]
    exact hsource
  · rw [Surgery.InnerDiscRegion.mergedGeometry_targetArc_length]
    exact htarget
  · rw [Surgery.InnerDiscRegion.mergedGeometry_sourceArc_length,
      Surgery.InnerDiscRegion.mergedGeometry_targetArc_length]
    exact hweight

end GloballyDistinguishedSectionFamily

end Family

/-- **The zero-cell pocket merge** (W1, Osin Lemma 9.7(a), and the zero-cell case of Lemma
9.7(b)).  Let `S` be a globally distinguished section family, `a ≠ b` two selected regions, and
`P` a pocket region of the optimal diagram, both sides disc regions, holding no relator cell and
avoided by every other selected region.  Let the inverse complement cycle of `P` read a reversed
arc of a cell `source`, a side, an arc of the target, and a side, with sides and side values no
longer than `ε`.  The target is a section, or a cell.  If a section, the target arc lies inside one
section.  If both arcs are nonempty and together at least as long as the arcs of `a` and `b`, there
is a contradiction. -/
def ZeroCellPocketMergeStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    ∀ a ∈ S.family, ∀ b ∈ S.family, a ≠ b →
      ∀ P : PocketRegion S.diagram, (∀ C ∈ S.diagram.relatorCells, C.face ∉ P.faces) →
        (∀ x ∈ S.family, x ≠ a → x ≠ b → Disjoint x.1 P.faces) →
        ∀ (source : Fin S.diagram.rCellCount) (target : Option (Fin S.diagram.rCellCount))
          (sourceArc : CyclicArc (cellDarts S.diagram source))
          (targetArc : CyclicArc (targetDarts S.diagram target))
          (rightSide leftSide : List S.diagram.toCombMap.Dart),
          invDarts S.diagram P.outer.cycle = sourceArc.reverseDarts ++ rightSide ++
            targetBoundaryDarts S.diagram target targetArc ++ leftSide →
          rightSide.length ≤ eps → leftSide.length ≤ eps →
          WordMetric.wordNorm D.alphabet.carrier
              (RelLetter.listVal (dartWord S.diagram rightSide)) ≤ eps →
          WordMetric.wordNorm D.alphabet.carrier
              (RelLetter.listVal (dartWord S.diagram leftSide)) ≤ eps →
          (target = none → ∃ j : Fin cuts.count,
            cuts.cut j.castSucc ≤ targetArc.start.1 ∧
              targetArc.start.1 + targetArc.length ≤ cuts.cut j.succ) →
          0 < sourceArc.length → 0 < targetArc.length →
          a.weight + b.weight ≤ sourceArc.length + targetArc.length → False

/-- **The zero-cell pocket merge holds.** -/
theorem zeroCellPocketMerge : ZeroCellPocketMergeStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S a ha b hb hab P hcells havoid source target
    sourceArc targetArc rightSide leftSide hdecomp hright hleft hrightNorm hleftNorm hsection
    hsource htarget hweight
  exact S.false_of_zeroCellPocket ha hb hab P hcells havoid sourceArc targetArc hdecomp hright
    hleft hrightNorm hleftNorm hsection hsource htarget hweight

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.false_of_disc_pair_singleton
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.false_of_zeroCellPocket
#audit_axioms GroupApproximation.GGT.VanKampen.ZeroCellPocketMergeStatement
#audit_closed_axioms GroupApproximation.GGT.VanKampen.zeroCellPocketMerge
