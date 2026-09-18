import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.Collapsed
import GroupApproximation.Meta.AxiomGuard

/-!
# Outer spur thickening preserves a clean two-gon: dart correspondence

Target: `GroupApproximation.GGT.VanKampen.TwoGonSpurStepStatement`.

Notation. `M := S.diagram.toCombMap`, `w := FaceEdgeDoubling.dart S.diagram outerFace j` (the
first corner `w_j` of the rebased outer boundary), `b := M.facePerm w` (the second corner).  The
spur hypothesis `hspur` says that the face across `w` is the outer face as well: `w` is a spur
edge of the outer boundary.  The thickened map `M'` is `EdgeInsertion.toCombMap M w b`, with darts
`Option (Option M.Dart)`; old darts enter through `embed z = some (some z)`, the new edge is
`{none, some none}`.  Each old region `r ∈ S.family` becomes `r' := regionCandidate ⟨r, _⟩`,
where the side condition `faceOf (alpha w) ∉ r.1` holds since `faceOf (alpha w) = outer` and the
outer face lies in no region (`spur_avoid`).

Mathematical proof.

(A) Crossings.  For every region `r`, side `s` and cell side `o`:
  `crossO r' s o = (crossO r s o).map embed`.  The source arc of `r'` is the source arc of `r`
  mapped by `embed`; the target arc is mapped by `targetImage`, which agrees with `embed` on every
  dart except `alpha w`, and `alpha w` is not on the target arc of `r`
  (`alpha_dart_not_mem_targetArc`, from `faceOf (alpha w) ∉ r.1`).  So the heads of the arcs are
  the images of the old heads.  The crossing on cell side `false` is `alpha` of the one on side
  `true`, `alpha` commutes with `embed` definitionally, and the Boolean selector of `crossO` on
  side `false` depends only on whether the target is `none`, which is preserved by
  `target' = target.map indexEquiv`.

(A') No crossing lies on an edge with the outer face on both sides.  A crossing on cell side
  `false` is on the boundary cycle of its region, so its face is in the region; a crossing on
  cell side `true` is `alpha` of a crossing on side `false`, so the face across it is in the
  region.  The outer face is in no region.

(T) The transport.  The map of regions is `regionFamilyEmbedding`, the new family is by
  definition its image, the relator cells are renumbered by `cellMap.indexEquiv`, source and
  target cells are carried by definition, target profiles by `regionCandidate_profile`, the darts
  by `embed`, and the crossings by (A).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur

open Equiv Embedded Embedded.RegionCandidate

universe u w v

section Crossings

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} (Delta : DiscDiagram.{u, w, v} W)
  (j : Fin (Delta.faceBoundary Delta.outerFace).darts.length)
  (hlen : 1 < (Delta.faceBoundary Delta.outerFace).darts.length)

/-- The target dart map agrees with the dart embedding away from `alpha w_j`. -/
theorem targetImage_eq (t : Option (Fin Delta.rCellCount)) {d : Delta.toCombMap.Dart}
    (hd : d ≠ Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) :
    OuterSpurThickening.targetImage Delta j hlen t d =
      (OuterSpurThickening.embedding Delta j hlen).darts d := by
  cases t with
  | none => exact OuterSpurThickening.outerImage_of_ne Delta j hlen hd
  | some _ => rfl

/-- The first dart of a carried source arc. -/
theorem sourceHead (a : OuterSpurThickening.Avoiding Delta j D eps) :
    (OuterSpurThickening.regionCandidate Delta j hlen a).2.sourceArc.darts.head? =
      a.val.2.sourceArc.darts.head?.map (OuterSpurThickening.embedding Delta j hlen).darts :=
  (congrArg List.head? (CyclicArc.mapTo_darts a.val.2.sourceArc
    (OuterSpurThickening.embedding Delta j hlen).darts
    (OuterSpurThickening.cellDarts_eq Delta j hlen a.val.2.source))).trans List.head?_map

/-- The first dart of a carried target arc. -/
theorem targetHead (a : OuterSpurThickening.Avoiding Delta j D eps) :
    (OuterSpurThickening.regionCandidate Delta j hlen a).2.targetArc.darts.head? =
      a.val.2.targetArc.darts.head?.map (OuterSpurThickening.embedding Delta j hlen).darts := by
  have h : (OuterSpurThickening.regionCandidate Delta j hlen a).2.targetArc.darts =
      a.val.2.targetArc.darts.map (OuterSpurThickening.embedding Delta j hlen).darts :=
    (CyclicArc.mapTo_darts a.val.2.targetArc
        (OuterSpurThickening.targetImage Delta j hlen a.val.2.target)
        (OuterSpurThickening.targetDarts_eq Delta j hlen a.val.2.target)).trans
      (List.map_congr_left fun d hd =>
        targetImage_eq Delta j hlen a.val.2.target fun h =>
          OuterSpurThickening.alpha_dart_not_mem_targetArc Delta j a.val.2 a.property (h ▸ hd))
  exact (congrArg List.head? h).trans List.head?_map

theorem cross_regionCandidate_true (a : OuterSpurThickening.Avoiding Delta j D eps)
    (s : Bool) :
    cross (OuterSpurThickening.regionCandidate Delta j hlen a) s true =
      (cross a.val s true).map (OuterSpurThickening.embedding Delta j hlen).darts := by
  cases s with
  | false => exact targetHead Delta j hlen a
  | true => exact sourceHead Delta j hlen a

theorem cross_regionCandidate (a : OuterSpurThickening.Avoiding Delta j D eps)
    (s o : Bool) :
    cross (OuterSpurThickening.regionCandidate Delta j hlen a) s o =
      (cross a.val s o).map (OuterSpurThickening.embedding Delta j hlen).darts := by
  cases o with
  | true => exact cross_regionCandidate_true Delta j hlen a s
  | false =>
    rw [cross_false, cross_false, cross_regionCandidate_true Delta j hlen a s]
    cases cross a.val s true with
    | none => rfl
    | some _ => rfl

/-- **(A) The crossings of a carried region are the carried crossings.** -/
theorem crossO_regionCandidate (a : OuterSpurThickening.Avoiding Delta j D eps)
    (s o : Bool) :
    crossO (OuterSpurThickening.regionCandidate Delta j hlen a) s o =
      (crossO a.val s o).map (OuterSpurThickening.embedding Delta j hlen).darts := by
  cases s with
  | true => exact cross_regionCandidate Delta j hlen a true o
  | false =>
    rcases Option.eq_none_or_eq_some a.val.2.target with ht | ⟨i, ht⟩
    · have ht' : (OuterSpurThickening.regionCandidate Delta j hlen a).2.target = none :=
        congrArg (Option.map (OuterSpurThickening.cellMap Delta j hlen).indexEquiv) ht
      rw [crossO_false_of_eq_none _ ht', crossO_false_of_eq_none _ ht]
      exact cross_regionCandidate Delta j hlen a false (!o)
    · have ht' : (OuterSpurThickening.regionCandidate Delta j hlen a).2.target =
          some ((OuterSpurThickening.cellMap Delta j hlen).indexEquiv i) :=
        congrArg (Option.map (OuterSpurThickening.cellMap Delta j hlen).indexEquiv) ht
      rw [crossO_false_of_eq_some _ ht', crossO_false_of_eq_some _ ht]
      exact cross_regionCandidate Delta j hlen a false o

/-- **(A') A dart with the outer face on both sides is no crossing.** -/
theorem not_crossO_of_outer (a : RegionCandidate D eps Delta) {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf d = Delta.outerFace)
    (hda : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = Delta.outerFace) (s o : Bool) :
    crossO a s o ≠ some d := by
  intro h
  cases o with
  | false =>
    exact OuterSpurThickening.outer_not_mem Delta a.2
      (by rw [← hd]; exact faceOf_crossO_false a h)
  | true =>
    have h' : crossO a s false = some (Delta.toCombMap.alpha d) := (crossO_alpha a s true d).mpr h
    exact OuterSpurThickening.outer_not_mem Delta a.2
      (by rw [← hda]; exact faceOf_crossO_false a h')

end Crossings

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **(T) The outer spur thickening transports the family.** -/
noncomputable def spurTransport (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (hspur : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
      (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) = S.diagram.outerFace) :
    RegionTransport S (OuterSpurThickening.sectionFamily S j hlen hspur) where
  map := OuterSpurThickening.regionFamilyEmbedding S.diagram j hlen S.family
    (OuterSpurThickening.spur_avoid S.diagram j hspur S.family)
  family_eq := rfl
  cellIndex := (OuterSpurThickening.cellMap S.diagram j hlen).indexEquiv
  source _ := rfl
  target _ := rfl
  profile a := OuterSpurThickening.regionCandidate_profile S.diagram j hlen
    ⟨a.1, OuterSpurThickening.spur_avoid S.diagram j hspur S.family a.1 a.2⟩
  darts := (OuterSpurThickening.embedding S.diagram j hlen).darts
  cross a s o := crossO_regionCandidate S.diagram j hlen
    ⟨a.1, OuterSpurThickening.spur_avoid S.diagram j hspur S.family a.1 a.2⟩ s o

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.targetImage_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.sourceHead
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.targetHead
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.cross_regionCandidate_true
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.cross_regionCandidate
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.crossO_regionCandidate
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.not_crossO_of_outer
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.spurTransport
