import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.Reduction
import GroupApproximation.Manuscript.NonMF.Full.GL03C.PocketListing

/-!
# The rose planarity core from a filtered walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  This is infrastructure for `thm:hull` in `non_mf_groups_exist.tex`
(around line 2121).

* `RoseFilterWalkStatement`: the geometric content of the rose step.  It asks for the extremal
  region `r` of `RoseExtremalJunctionStatement` with the source cell `K.source`, and:
  - the darts of the pocket boundary kept by the move form a nonempty walk in cycle order;
  - the kept part of the source arc is an arc, and so is the kept part of the target arc, which
    stays between `lo` and `hi`.
* `roseExtremalJunction_of_filterWalk` (proved): it implies
  `P10RoseExtremalTrim.RoseExtremalJunctionStatement`, through `junction_listing_of_filter`.

This module imports the live rose chain.  That chain contains `P10Rose/Live/Move` and
`P10Rose/Live/Reduction`, last changed by a commit whose message contains "WIP", so this module is
kept at its final path and is not landed until that chain is cleared.
-/

namespace GroupApproximation.Full.GL03C

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove
open GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.SubArcMove

/-- **The move of an extremal region keeps a walk in cycle order, with sub-arcs** (Osin 9.7(b),
infrastructure for `thm:hull`, `non_mf_groups_exist.tex`).  Under the hypotheses of
`RoseExtremalJunctionStatement`, some dart `r` has a face class that avoids the exterior face and
meets the cycle.  Flipping that class keeps the cell `K.source` out and some cell `kept` in.  The
kept darts of the cycle, in cycle order, form a nonempty walk.  The kept part of the source arc is
a proper arc, and so is the kept part of the target arc, which stays between `lo` and `hi`. -/
def RoseFilterWalkStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      GreendlingerLeaf.P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ r : X.toCombMap.Dart,
          (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
            (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
          (∃ y ∈ K.boundary.cycle, Relation.EqvGen
            (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r y ∨
            Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
              (walkKeep X.toCombMap K.boundary.cycle)) r (X.toCombMap.alpha y)) ∧
          ∃ kept : Fin X.rCellCount,
            (cell X K.source).face ∉ flipFaces X.toCombMap K.faces
              (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
            (cell X kept).face ∈ flipFaces X.toCombMap K.faces
              (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
            K.boundary.cycle.filter (movePred X.toCombMap
              (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r)) ≠ [] ∧
            (K.boundary.cycle.filter (movePred X.toCombMap
              (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))).IsChain
              (fun d e => X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
            (∃ t₁' : CyclicArc (cellDarts X K.source),
              K.sourceArc.darts.filter (fun d => movePred X.toCombMap
                (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r)
                (X.toCombMap.alpha d)) = t₁'.darts ∧
              t₁'.length < (cellDarts X K.source).length) ∧
            ∃ t₂' : CyclicArc (outerDarts X),
              K.targetArc.darts.filter (movePred X.toCombMap
                (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r)) =
                t₂'.darts ∧
              lo ≤ t₂'.start.1 ∧ t₂'.start.1 + t₂'.length ≤ hi ∧
              t₂'.length < (outerDarts X).length

/-- **The rose planarity core from a filtered walk** (Osin 9.7(b), infrastructure for `thm:hull`,
`non_mf_groups_exist.tex`): list the kept darts block by block with
`junction_listing_of_filter`. -/
theorem roseExtremalJunction_of_filterWalk (h : RoseFilterWalkStatement.{u, w, v}) :
    GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hrout, hry, kept, hsource, hkept, hne, hchain, ⟨t₁', hA, ht₁'⟩, t₂', hB, hlo,
    hhi, ht₂'⟩ := h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨s₁, s₂, hperm, hne', hs₁c, hs₂c, hj₁, hj₂, hj₃, hs₁, hs₂⟩ :=
    junction_listing_of_filter K _ hne hchain hA hB
  exact ⟨r, hrout, hry, K.source, kept, hsource, hkept, t₁', t₂', s₁, s₂, hperm, hne', hs₁c,
    hs₂c, hj₁, hj₂, hj₃, hs₁, hs₂, hlo, hhi, ht₁', ht₂'⟩

end GroupApproximation.Full.GL03C
