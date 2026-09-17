import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.Bypass
import GroupApproximation.Meta.AxiomGuard

/-!
# One region-pair thickening step as a transport of the family

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), and the assumption before Lemma 9.3.

Notation. `X := S.diagram`, `M := X.toCombMap`, `w := FaceEdgeDoubling.dart X f j` (the side dart
of the region `T.holder` holding `f`), `X' := FaceEdgeDoubling.diagram X f j hlen hf`, whose darts
are `Option (Option M.Dart)`, with old darts entering through `embed z = some (some z)`.

Mathematical proof.

(A) Arcs. The holder is carried by `Holding.holdingCandidate`; its source arc is mapped by
  `carrierImage`, its target arc by `targetImage`, and both maps agree with `embed` off `w`.
  Since `w` lies on a side of the holder, the boundary cycle is duplicate free and the face across
  `w` is outside the holder, so `w` lies on neither arc (`Holding.dart_not_mem_*_of_side`). Every
  other region is carried by `regionCandidateOfArcs`, whose arcs avoid `w` by `T.avoid`. Hence
  in both cases the arc darts of the carried region are the images under `embed` of the old ones.

(B) Crossings. `cross r s true` is the head of an arc, and `cross r s false` is its `alpha`, which
  commutes with `embed` definitionally. The selector of `crossO r false` only depends on whether
  the target is `none`, preserved by `target' = target.map indexEquiv`. So
  `crossO r' s o = (crossO r s o).map embed`.

(C) Transport. `stepEquiv` is a bijection of the old family with the new one, which gives the
  embedding of regions and `family_eq`; source, target, profile and crossings are those of (A),
  (B), case by case on whether the region is the holder.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair

open Equiv Embedded Embedded.RegionCandidate

universe u w v

section Arcs

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}
  (X : DiscDiagram.{u, w, v} W) (f : X.toCombMap.Face)
  (j : Fin (X.faceBoundary f).darts.length)
  (hlen : 1 < (X.faceBoundary f).darts.length) (hf : f ≠ X.outerFace)

theorem cross_true_of_arcs (a : RegionCandidate D eps X)
    (a' : RegionCandidate D eps (FaceEdgeDoubling.diagram X f j hlen hf))
    (hsrc : a'.2.sourceArc.darts =
      a.2.sourceArc.darts.map (FaceEdgeDoubling.embedding X f j hlen hf).darts)
    (htgt : a'.2.targetArc.darts =
      a.2.targetArc.darts.map (FaceEdgeDoubling.embedding X f j hlen hf).darts)
    (s : Bool) :
    cross a' s true = (cross a s true).map (FaceEdgeDoubling.embedding X f j hlen hf).darts := by
  cases s with
  | false => exact (congrArg List.head? htgt).trans List.head?_map
  | true => exact (congrArg List.head? hsrc).trans List.head?_map

theorem cross_of_arcs (a : RegionCandidate D eps X)
    (a' : RegionCandidate D eps (FaceEdgeDoubling.diagram X f j hlen hf))
    (hsrc : a'.2.sourceArc.darts =
      a.2.sourceArc.darts.map (FaceEdgeDoubling.embedding X f j hlen hf).darts)
    (htgt : a'.2.targetArc.darts =
      a.2.targetArc.darts.map (FaceEdgeDoubling.embedding X f j hlen hf).darts)
    (s o : Bool) :
    cross a' s o = (cross a s o).map (FaceEdgeDoubling.embedding X f j hlen hf).darts := by
  cases o with
  | true => exact cross_true_of_arcs X f j hlen hf a a' hsrc htgt s
  | false =>
    rw [cross_false, cross_false, cross_true_of_arcs X f j hlen hf a a' hsrc htgt s]
    cases cross a s true with
    | none => rfl
    | some _ => rfl

/-- **(B) Crossings through carried arcs.** -/
theorem crossO_of_arcs (a : RegionCandidate D eps X)
    (a' : RegionCandidate D eps (FaceEdgeDoubling.diagram X f j hlen hf))
    (hsrc : a'.2.sourceArc.darts =
      a.2.sourceArc.darts.map (FaceEdgeDoubling.embedding X f j hlen hf).darts)
    (htgt : a'.2.targetArc.darts =
      a.2.targetArc.darts.map (FaceEdgeDoubling.embedding X f j hlen hf).darts)
    (ht : a'.2.target = a.2.target.map (FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv)
    (s o : Bool) :
    crossO a' s o = (crossO a s o).map (FaceEdgeDoubling.embedding X f j hlen hf).darts := by
  cases s with
  | true => exact cross_of_arcs X f j hlen hf a a' hsrc htgt true o
  | false =>
    rcases Option.eq_none_or_eq_some a.2.target with ht0 | ⟨i, ht0⟩
    · have ht' : a'.2.target = none :=
        ht.trans (congrArg (Option.map (FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv) ht0)
      rw [crossO_false_of_eq_none _ ht', crossO_false_of_eq_none _ ht0]
      exact cross_of_arcs X f j hlen hf a a' hsrc htgt false (!o)
    · have ht' : a'.2.target = some ((FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv i) :=
        ht.trans (congrArg (Option.map (FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv) ht0)
      rw [crossO_false_of_eq_some _ ht', crossO_false_of_eq_some _ ht0]
      exact cross_of_arcs X f j hlen hf a a' hsrc htgt false o

variable {family : Finset (RegionCandidate D eps X)}

/-- **(A) The source arc of the carried holder.** -/
theorem holding_sourceArc (T : RegionPairThickening.StepData X f j family) :
    (RegionPairThickening.holding X f j hlen hf T).2.sourceArc.darts =
      T.holder.2.sourceArc.darts.map (FaceEdgeDoubling.embedding X f j hlen hf).darts :=
  FaceEdgeDoubling.mapTo_darts_of_avoid X f j hlen hf T.holder.2.sourceArc
    (FaceEdgeDoubling.carrierImage X f j hlen hf (Embedded.cell X T.holder.2.source).face)
    (fun _ hd => FaceEdgeDoubling.carrierImage_of_ne_dart X f j hlen hf _ hd)
    (FaceEdgeDoubling.cellDarts_eq X f j hlen hf T.holder.2.source)
    (FaceEdgeDoubling.dart_not_mem_sourceArc X f j T.holder.2
      (FaceEdgeDoubling.Holding.faceOf_alpha_dart_not_mem_of_side X f j T.holder.2 T.side))

/-- **(A) The target arc of the carried holder.** -/
theorem holding_targetArc (T : RegionPairThickening.StepData X f j family) :
    (RegionPairThickening.holding X f j hlen hf T).2.targetArc.darts =
      T.holder.2.targetArc.darts.map (FaceEdgeDoubling.embedding X f j hlen hf).darts :=
  FaceEdgeDoubling.mapTo_darts_of_avoid X f j hlen hf T.holder.2.targetArc
    (FaceEdgeDoubling.targetImage X f j hlen hf T.holder.2.target)
    (fun _ hd => FaceEdgeDoubling.targetImage_of_ne_dart X f j hlen hf _ hd)
    (FaceEdgeDoubling.targetDarts_eq X f j hlen hf T.holder.2.target)
    (FaceEdgeDoubling.Holding.dart_not_mem_targetArc_of_side' X f j T.holder.2 T.side)

/-- **(A) The source arc of a region carried along its arcs.** -/
theorem carried_sourceArc (a : FaceEdgeDoubling.ArcAvoiding X f j D eps) :
    (FaceEdgeDoubling.regionCandidateOfArcs X f j hlen hf a).2.sourceArc.darts =
      a.val.2.sourceArc.darts.map (FaceEdgeDoubling.embedding X f j hlen hf).darts :=
  FaceEdgeDoubling.mapTo_darts_of_avoid X f j hlen hf a.val.2.sourceArc
    (FaceEdgeDoubling.carrierImage X f j hlen hf (Embedded.cell X a.val.2.source).face)
    (fun _ hd => FaceEdgeDoubling.carrierImage_of_ne_dart X f j hlen hf _ hd)
    (FaceEdgeDoubling.cellDarts_eq X f j hlen hf a.val.2.source) a.property.2.1

/-- **(A) The target arc of a region carried along its arcs.** -/
theorem carried_targetArc (a : FaceEdgeDoubling.ArcAvoiding X f j D eps) :
    (FaceEdgeDoubling.regionCandidateOfArcs X f j hlen hf a).2.targetArc.darts =
      a.val.2.targetArc.darts.map (FaceEdgeDoubling.embedding X f j hlen hf).darts :=
  FaceEdgeDoubling.mapTo_darts_of_avoid X f j hlen hf a.val.2.targetArc
    (FaceEdgeDoubling.targetImage X f j hlen hf a.val.2.target)
    (fun _ hd => FaceEdgeDoubling.targetImage_of_ne_dart X f j hlen hf _ hd)
    (FaceEdgeDoubling.targetDarts_eq X f j hlen hf a.val.2.target) a.property.2.2

/-- The avoidance data of a region other than the holder. -/
theorem avoid_of_ne (T : RegionPairThickening.StepData X f j family) (a : family)
    (h : a.val ≠ T.holder) :
    f ∉ a.val.1 ∧ FaceEdgeDoubling.dart X f j ∉ a.val.2.sourceArc.darts ∧
      FaceEdgeDoubling.dart X f j ∉ a.val.2.targetArc.darts :=
  T.avoid a.val (Finset.mem_erase.mpr ⟨h, a.property⟩)

theorem stepMap_crossO (T : RegionPairThickening.StepData X f j family) (a : family) (s o : Bool) :
    crossO (RegionPairThickening.stepMap X f j hlen hf T a).val s o =
      (crossO a.val s o).map (FaceEdgeDoubling.embedding X f j hlen hf).darts := by
  by_cases ha : a.val = T.holder
  · rw [RegionPairThickening.stepMap_val_of_eq X f j hlen hf T ha, ha]
    exact crossO_of_arcs X f j hlen hf T.holder (RegionPairThickening.holding X f j hlen hf T)
      (holding_sourceArc X f j hlen hf T) (holding_targetArc X f j hlen hf T) rfl s o
  · rw [RegionPairThickening.stepMap_val_of_ne X f j hlen hf T ha]
    exact crossO_of_arcs X f j hlen hf a.val
      (FaceEdgeDoubling.regionCandidateOfArcs X f j hlen hf ⟨a.val, avoid_of_ne X f j T a ha⟩)
      (carried_sourceArc X f j hlen hf ⟨a.val, avoid_of_ne X f j T a ha⟩)
      (carried_targetArc X f j hlen hf ⟨a.val, avoid_of_ne X f j T a ha⟩) rfl s o

theorem stepMap_source (T : RegionPairThickening.StepData X f j family) (a : family) :
    (RegionPairThickening.stepMap X f j hlen hf T a).val.2.source =
      (FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv a.val.2.source := by
  by_cases ha : a.val = T.holder
  · rw [RegionPairThickening.stepMap_val_of_eq X f j hlen hf T ha, ha]
    rfl
  · rw [RegionPairThickening.stepMap_val_of_ne X f j hlen hf T ha]
    rfl

theorem stepMap_target (T : RegionPairThickening.StepData X f j family) (a : family) :
    (RegionPairThickening.stepMap X f j hlen hf T a).val.2.target =
      a.val.2.target.map (FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv := by
  by_cases ha : a.val = T.holder
  · rw [RegionPairThickening.stepMap_val_of_eq X f j hlen hf T ha, ha]
    rfl
  · rw [RegionPairThickening.stepMap_val_of_ne X f j hlen hf T ha]
    rfl

/-- The regions of the step, as an embedding of the old family. -/
noncomputable def stepEmbedding (T : RegionPairThickening.StepData X f j family) :
    family ↪ RegionCandidate D eps (FaceEdgeDoubling.diagram X f j hlen hf) :=
  (RegionPairThickening.stepEquiv X f j hlen hf T).toEmbedding.trans (Function.Embedding.subtype _)

theorem stepEmbedding_apply (T : RegionPairThickening.StepData X f j family) (a : family) :
    stepEmbedding X f j hlen hf T a = (RegionPairThickening.stepMap X f j hlen hf T a).val :=
  rfl

end Arcs

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **(C) The region-pair thickening step transports the family.** -/
noncomputable def stepTransport (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (T : RegionPairThickening.StepData S.diagram f j S.family) :
    RegionTransport S (RegionPairThickening.sectionFamily S f j hlen hf T) where
  map := stepEmbedding S.diagram f j hlen hf T
  family_eq := by
    ext b
    constructor
    · intro hb
      obtain ⟨a, ha⟩ := (RegionPairThickening.stepEquiv S.diagram f j hlen hf T).surjective ⟨b, hb⟩
      exact Finset.mem_map.mpr ⟨a, Finset.mem_attach _ _, congrArg Subtype.val ha⟩
    · intro hb
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hb
      exact (RegionPairThickening.stepEquiv S.diagram f j hlen hf T a).property
  cellIndex := (FaceEdgeDoubling.cellMap S.diagram f j hlen hf).indexEquiv
  source a := stepMap_source S.diagram f j hlen hf T a
  target a := stepMap_target S.diagram f j hlen hf T a
  profile a := RegionPairThickening.stepEquiv_profile S.diagram f j hlen hf T a
  darts := (FaceEdgeDoubling.embedding S.diagram f j hlen hf).darts
  cross a s o := stepMap_crossO S.diagram f j hlen hf T a s o

theorem stepTransport_map (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (T : RegionPairThickening.StepData S.diagram f j S.family) (a : S.family) :
    (stepTransport S f j hlen hf T).map a =
      (RegionPairThickening.stepMap S.diagram f j hlen hf T a).val :=
  rfl

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.crossO_of_arcs
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.stepMap_crossO
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.stepTransport
