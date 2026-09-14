import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSubdiagram
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLoopCut
import GroupApproximation.Meta.AxiomGuard

/-!
# The loop cut from the subdiagram enclosed by a closed walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): "it is easy to show that `Φ_M` can not
contain loops either.  The only difference is that the subdiagram `Ξ` will be bounded by `st`,
where `l(s) < ε` and `t` is a subpath of `∂Π_1`."

`nonempty_osinLoopCut_of_pocketRegion` (`OsinPocketLoopCut`) builds the loop cut from a pocket
region, whose walk is simple.  In the island case of binder 3 (Case 1 of Lemma 9.4) the side runs
through a cutting path `t` around an island, so the walk uses both darts of the edges of `t` and
the enclosed faces are joined only along `t`.  This file names the loop cut at that generality,
over an enclosed face set (`ClosedWalkEnclosedSubdiagram.EnclosedFaceSet`) in place of a pocket
region.

* `EnclosedSubdiagramLoopCutStatement`: the hypotheses of `nonempty_osinLoopCut_of_pocketRegion`,
  with an enclosed face set and its outside walk in place of the pocket region and its two
  boundary-following conditions, give a loop cut of `Δ`.
* `twoPartSectionCuts`, `twoPartSectionCuts_count`, `twoPartSectionCuts_side_short`: the two
  sections `g · arc` on a boundary word that splits into two quasi-geodesic parts.
* `OsinLoopCut.ofTwoPartBoundary`: any least-area disc diagram with at least one and fewer relator
  cells than `Δ`, reading a short side `g` and then an arc, is a loop cut of `Δ` once regions to
  the arc glue back.  `OsinLoopCut.ofPocketRegion` is the case of the pocket diagram.

The producer composes the enclosed subdiagram (`ClosedWalkEnclosedSubdiagramStatement`), a
geodesic collar along `s` and the transport of regions to `t`.  The named pieces for the collar and
the transport are fixed after lane ms-intro-1's audit of `DiscDiagram.ofPlanar`,
`isRelatorProduct_of_planar`, `Surgery.InnerDiscRegion` and the zero-cell merge.  The consumer is
`OsinLemma94CaseOneIslandStatement` (lane ms-intro-1), through `OsinLoopCut.false_of_below`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemmas 9.4 and 9.7); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric

/-- **The loop cut from an enclosed face set.**  Let `Δ` be least area and `X` an O-equivalent copy
with labels in the symmetric label alphabet.  Take a face set of `X` enclosed by an outside walk,
with a relator cell inside and a cell `i` outside.  Let the inverse walk read a side `s` and an arc
of `i` backwards, with side value of word norm at most `ε`.  Under `C(ε, μ, λ, c, ρ)` with `λ ≤ 1`
and `0 ≤ c`, there is a loop cut of `Δ`. -/
def EnclosedSubdiagramLoopCutStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ),
    OsinCCondition D W eps mu lambda c rho → lambda ≤ 1 → 0 ≤ c →
    ∀ (Delta X : DiscDiagram.{u, w, v} W), Delta.LeastArea → OEquivalentDiscDiagram Delta X →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
        EnclosedFaceSet X faces outerWalk →
        ∀ C ∈ X.relatorCells, C.face ∈ faces →
        ∀ i : Fin X.rCellCount, (cell X i).face ∉ faces →
        ∀ (A : CyclicArc (cellDarts X i)) (s : List X.toCombMap.Dart),
          invDarts X outerWalk = s ++ invDarts X A.darts →
          wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s)) ≤ eps →
            Nonempty (OsinLoopCut D lambda c eps Delta)

/-- **Two sections on a two-part boundary word**: a side `g` followed by an arc word, both
`(λ, c)`-quasi-geodesic. -/
noncomputable def twoPartSectionCuts {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (D : RelGenSet G Lambda) (lambda c : ℝ)
    (Xi : DiscDiagram.{u, w, v} W) (g arc : List (RelLetter G Lambda))
    (hword : Xi.boundaryWord = g ++ arc)
    (hquasi : ∀ part ∈ [g, arc], IsLambdaCQuasiGeodesicWord D lambda c part) :
    SectionCuts D lambda c Xi.boundaryWord :=
  SectionCuts.ofParts [g, arc] (hword.trans (by simp)) (by simp) (by simp) hquasi

/-- The two-part section cuts have two sections. -/
theorem twoPartSectionCuts_count {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (D : RelGenSet G Lambda) (lambda c : ℝ)
    (Xi : DiscDiagram.{u, w, v} W) (g arc : List (RelLetter G Lambda))
    (hword : Xi.boundaryWord = g ++ arc)
    (hquasi : ∀ part ∈ [g, arc], IsLambdaCQuasiGeodesicWord D lambda c part) :
    (twoPartSectionCuts D lambda c Xi g arc hword hquasi).count = 2 :=
  rfl

/-- Section `0` of the two-part section cuts, the side `g`, is no longer than `ε` when `g` is. -/
theorem twoPartSectionCuts_side_short {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (Xi : DiscDiagram.{u, w, v} W) (g arc : List (RelLetter G Lambda))
    (hword : Xi.boundaryWord = g ++ arc)
    (hquasi : ∀ part ∈ [g, arc], IsLambdaCQuasiGeodesicWord D lambda c part)
    (hg : g.length ≤ eps) :
    ∀ j : Fin (twoPartSectionCuts D lambda c Xi g arc hword hquasi).count, (j : ℕ) = 0 →
      (twoPartSectionCuts D lambda c Xi g arc hword hquasi).cut j.succ -
          (twoPartSectionCuts D lambda c Xi g arc hword hquasi).cut j.castSucc ≤ eps := by
  have key : ∀ (k : ℕ) (hk : k < 2), k = 0 → ([g, arc].get ⟨k, hk⟩).length ≤ eps := by
    intro k hk hk'
    subst hk'
    exact hg
  intro j hj
  refine (SectionCuts.ofParts_cut_sub [g, arc] (hword.trans (by simp)) (by simp) (by simp)
    hquasi j).trans_le ?_
  exact key j j.isLt hj

/-- **The loop cut from a two-part boundary.**  Let `Δ` be least area.  A least-area disc diagram
`Ξ` with at least one relator cell and fewer than `Δ`, whose boundary word reads a side `g` of
length at most `ε` followed by an arc word, both `(λ, c)`-quasi-geodesic, is a loop cut of `Δ` as
soon as regions to the arc in O-equivalent copies of `Ξ` glue back into cell-to-cell regions of
O-equivalent copies of `Δ`.  This is `OsinLoopCut.ofPocketRegion` with the pocket diagram replaced
by any such `Ξ`, for instance an enclosed subdiagram after a geodesic collar. -/
noncomputable def OsinLoopCut.ofTwoPartBoundary {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} (Xi : DiscDiagram.{u, w, v} W)
    (hlea : Xi.LeastArea) (hpos : 0 < Xi.rCellCount) (hlt : Xi.rCellCount < Delta.rCellCount)
    (g arc : List (RelLetter G Lambda)) (hword : Xi.boundaryWord = g ++ arc)
    (hquasi : ∀ part ∈ [g, arc], IsLambdaCQuasiGeodesicWord D lambda c part)
    (hg : g.length ≤ eps)
    (htransport :
      ∀ j : Fin (twoPartSectionCuts D lambda c Xi g arc hword hquasi).count, (j : ℕ) = 1 →
        ∀ (Xi' : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram Xi Xi' →
          ∀ a : RegionCandidate D eps Xi',
            RegionCandidate.TargetsSectionIndex
                (twoPartSectionCuts D lambda c Xi g arc hword hquasi) j a →
              ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y)
                (k : Fin Y.rCellCount),
                Nonempty (OEquivalentDiscDiagram Delta Y) ∧
                  b.2.target = some k ∧ b.2.source ≠ k ∧
                  b.contiguityDegree = a.contiguityDegree) :
    OsinLoopCut D lambda c eps Delta where
  enclosed := Xi
  leastArea := hlea
  rCellCount_pos := hpos
  rCellCount_lt := hlt
  sections := twoPartSectionCuts D lambda c Xi g arc hword hquasi
  count_eq := twoPartSectionCuts_count D lambda c Xi g arc hword hquasi
  side_short := twoPartSectionCuts_side_short D lambda c eps Xi g arc hword hquasi hg
  transport := htransport

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.EnclosedSubdiagramLoopCutStatement
#audit_axioms GroupApproximation.GGT.VanKampen.twoPartSectionCuts
#audit_axioms GroupApproximation.GGT.VanKampen.twoPartSectionCuts_count
#audit_axioms GroupApproximation.GGT.VanKampen.twoPartSectionCuts_side_short
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLoopCut.ofTwoPartBoundary
