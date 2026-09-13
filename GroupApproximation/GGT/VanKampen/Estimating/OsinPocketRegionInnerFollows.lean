import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFirstTurnWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketDiscMerge
import GroupApproximation.GGT.VanKampen.SurgeryReclosedPlanarity
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket region of a noncrossing walk whose inner cycle follows its boundary

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.7(a): "otherwise one can include the
ε-contiguity subdiagrams corresponding to the edges `e` and `f` of `Φ'_M` into a single
ε-contiguity subdiagram in the obvious way, contrary to the definition of `M`."

`PocketRegion.ofNoncrossingClosedWalk` builds the pocket region of a noncrossing closed walk when
the reversed walk follows the boundary of the other side.  In a lake the outer sides of the two
regions touch at a vertex, the complement of the merged face set falls into the exterior piece and
a lake holding the cell, and the reversed walk does not follow its boundary
(`OsinPocketLakeModel.lakeCycle_outerCycle_not_followsBoundary`).  The walk itself does follow
(`OsinPocketLakeModel.lakeCycle_innerCycle_followsBoundary`).  A disc region needs only a connected
reclosed map with the Euler characteristic of the map, so the complement is still a disc region:
the reversed walk is noncrossing (`IsNoncrossingClosedWalk.reverseMapAlpha`), its side is the other
side of the walk, and its outer cycle is the walk, so the Euler lemma for noncrossing walks
(`IsNoncrossingClosedWalk.reclosed_euler`) applies to it.

* `IsNoncrossingClosedWalk.exists_walkClass`: every dart lies in the face class of a dart of the
  walk or of a dart of the reversed walk.  The union of the two classes is closed under the
  elementary moves of the map, and the map is connected.
* `IsNoncrossingClosedWalk.sideFaces_reverseMapAlpha`: the side of the reversed walk is the other
  side of the walk.  One inclusion is `FirstTurnWalk.not_mem_sideFaces`.
* `IsNoncrossingClosedWalk.reclosed_euler_outer_of_innerFollows`: when the inner cycle follows its
  boundary, the reclosed map of the other side has the Euler characteristic of the map.
* `IsNoncrossingClosedWalk.outerDiscRegion_of_innerFollows`: the other side is a disc region with
  the reversed walk as its cycle.
* `PocketRegion.ofNoncrossingClosedWalkInner`: the pocket region on the walk's side.  Its cycle is
  the walk and its complement's cycle is the reversed walk.
* `Surgery.InnerDiscRegion.ofNoncrossingClosedWalkInner`: with no relator cell on the side, the
  collapsible disc region whose cycle is the walk.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(a);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv Surgery.MapCollapse SimpleClosedWalkSides

universe u w v

namespace Surgery.MapCollapse.BoundaryCycle

/-- Following the boundary depends only on the face set and the cycle. -/
theorem followsBoundary_of_faces_eq {M : CombMap.{u}} {faces₁ faces₂ : Finset M.Face}
    (h : faces₁ = faces₂) (b₁ : BoundaryCycle M faces₁) (b₂ : BoundaryCycle M faces₂)
    (hc : b₁.cycle = b₂.cycle) (hb : b₁.FollowsBoundary) : b₂.FollowsBoundary := by
  subst h
  obtain ⟨c₁, _, _, _⟩ := b₁
  obtain ⟨c₂, _, _, _⟩ := b₂
  obtain rfl : c₁ = c₂ := hc
  exact hb

/-- The Euler characteristic of a reclosed map depends only on the face set and the cycle. -/
theorem reclosedMap_euler_of_faces_eq {M : CombMap.{u}} {faces₁ faces₂ : Finset M.Face}
    (h : faces₁ = faces₂) (b₁ : BoundaryCycle M faces₁) (b₂ : BoundaryCycle M faces₂)
    (hc : b₁.cycle = b₂.cycle) :
    (reclosedMap M faces₁ b₁).eulerCharacteristic =
      (reclosedMap M faces₂ b₂).eulerCharacteristic := by
  subst h
  obtain ⟨c₁, _, _, _⟩ := b₁
  obtain ⟨c₂, _, _, _⟩ := b₂
  obtain rfl : c₁ = c₂ := hc
  rfl

end Surgery.MapCollapse.BoundaryCycle

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

/-- The darts in the face class of a dart of `w` or of a dart of the reversed walk, advancing
around faces and crossing edges off `w`. -/
def WalkClass (M : CombMap.{u}) (w : List M.Dart) (x : M.Dart) : Prop :=
  (∃ d ∈ w, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) d x) ∨
    ∃ d ∈ w.reverse.map M.alpha, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) d x

theorem walkClass_of_eqvGen {x y : M.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x y)
    (hx : WalkClass M w x) : WalkClass M w y := by
  rcases hx with ⟨d, hd, hdx⟩ | ⟨d, hd, hdx⟩
  · exact Or.inl ⟨d, hd, .trans _ _ _ hdx h⟩
  · exact Or.inr ⟨d, hd, .trans _ _ _ hdx h⟩

theorem walkClass_alpha {x : M.Dart} (hx : WalkClass M w x) : WalkClass M w (M.alpha x) := by
  by_cases hk : walkKeep M w x
  · rcases hk with hxw | hxw
    · exact Or.inr ⟨M.alpha x, List.mem_map.mpr ⟨x, List.mem_reverse.mpr hxw, rfl⟩, .refl _⟩
    · exact Or.inl ⟨M.alpha x, hxw, .refl _⟩
  · exact walkClass_of_eqvGen (.rel _ _ (Or.inr ⟨hk, rfl⟩)) hx

theorem facePerm_alpha_eq_sigma (M : CombMap.{u}) (x : M.Dart) :
    M.facePerm (M.alpha x) = M.sigma x := by
  show M.sigma (M.alpha (M.alpha x)) = M.sigma x
  rw [M.alpha_involutive x]

theorem walkClass_sigma {x : M.Dart} (hx : WalkClass M w x) : WalkClass M w (M.sigma x) := by
  have h := walkClass_of_eqvGen (.rel _ _ (Or.inl rfl)) (walkClass_alpha hx)
  rwa [facePerm_alpha_eq_sigma] at h

theorem walkClass_of_sigma {x : M.Dart} (hx : WalkClass M w (M.sigma x)) : WalkClass M w x := by
  have hstep : CombMap.FaceClassStep M (walkKeep M w) (M.alpha x) (M.sigma x) :=
    Or.inl (facePerm_alpha_eq_sigma M x).symm
  have h := walkClass_alpha (walkClass_of_eqvGen (.symm _ _ (.rel _ _ hstep)) hx)
  rwa [M.alpha_involutive x] at h

/-- **Every dart lies in the face class of the walk or of the reversed walk**: the union of the
two classes is closed under the elementary moves of the map and meets the first dart of the walk,
and the map is connected. -/
theorem exists_walkClass (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) (x : M.Dart) :
    WalkClass M w x := by
  have hiff : ∀ {y z : M.Dart}, Relation.EqvGen M.Adjacent y z →
      (WalkClass M w y ↔ WalkClass M w z) := by
    intro y z h
    induction h with
    | rel a b hab =>
      rcases hab with hab | hab
      · subst hab
        refine ⟨walkClass_alpha, fun hb => ?_⟩
        have h := walkClass_alpha hb
        rwa [M.alpha_involutive a] at h
      · subst hab
        exact ⟨walkClass_sigma, walkClass_of_sigma⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (hiff (hM.1 (w.head hw.ne_nil) x)).mp
    (Or.inl ⟨w.head hw.ne_nil, List.head_mem hw.ne_nil, .refl _⟩)

/-- **The side of the reversed walk is the other side of the walk.** -/
theorem sideFaces_reverseMapAlpha (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) :
    sideFaces M (w.reverse.map M.alpha) = sideOutside M w := by
  ext f
  rw [mem_sideOutside_iff]
  constructor
  · intro hf hfw
    exact FirstTurnWalk.not_mem_sideFaces hM (hw.reverseMapAlpha hM) hfw hf
  · intro hf
    revert hf
    refine Quotient.inductionOn' f ?_
    intro x hx
    change M.faceOf x ∉ sideFaces M w at hx
    change M.faceOf x ∈ sideFaces M (w.reverse.map M.alpha)
    rw [mem_sideFaces_iff, FirstTurnWalk.walkKeep_reverse_map_alpha]
    rcases hw.exists_walkClass hM x with h | h
    · exact absurd ((mem_sideFaces_iff M w x).mpr h) hx
    · exact h

/-- **The other side of the reversed walk is the side of the walk.** -/
theorem sideOutside_reverseMapAlpha (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) :
    sideOutside M (w.reverse.map M.alpha) = sideFaces M w := by
  ext f
  rw [mem_sideOutside_iff, hw.sideFaces_reverseMapAlpha hM, mem_sideOutside_iff, not_not]

/-- **The Euler equality of the other side, from inner following.**  The reversed walk is
noncrossing, its outer cycle is the walk, which follows its boundary, and its side is the other
side of the walk, so `reclosed_euler` applies to it. -/
theorem reclosed_euler_outer_of_innerFollows (hw : IsNoncrossingClosedWalk M w)
    (hM : M.IsPlanar) (hin : (hw.innerCycle hM).FollowsBoundary) :
    (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).eulerCharacteristic =
      M.eulerCharacteristic := by
  have hw' := hw.reverseMapAlpha hM
  have hout' : (hw'.outerCycle hM).FollowsBoundary :=
    BoundaryCycle.followsBoundary_of_faces_eq (hw.sideOutside_reverseMapAlpha hM).symm
      (hw.innerCycle hM) (hw'.outerCycle hM)
      (FirstTurnWalk.reverse_map_alpha_involutive w).symm hin
  exact (BoundaryCycle.reclosedMap_euler_of_faces_eq (hw.sideFaces_reverseMapAlpha hM)
    (hw'.innerCycle hM) (hw.outerCycle hM) rfl).symm.trans (hw'.reclosed_euler hM hout')

/-- **The other side is a disc region**, with the reversed walk as its cycle, when the inner
cycle follows its boundary. -/
noncomputable def outerDiscRegion_of_innerFollows (hw : IsNoncrossingClosedWalk M w)
    (hM : M.IsPlanar) (hin : (hw.innerCycle hM).FollowsBoundary) :
    IsDiscRegion M (sideOutside M w) :=
  (hw.outerCycle hM).toDiscRegion_of_euler M _ hM.1 (hw.reclosed_euler_outer_of_innerFollows hM hin)

theorem outerDiscRegion_of_innerFollows_cycle (hw : IsNoncrossingClosedWalk M w)
    (hM : M.IsPlanar) (hin : (hw.innerCycle hM).FollowsBoundary) :
    (hw.outerDiscRegion_of_innerFollows hM hin).cycle = w.reverse.map M.alpha :=
  rfl

end IsNoncrossingClosedWalk

namespace PocketRegion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} {walk : List Delta.toCombMap.Dart}

/-- **The pocket region of a noncrossing closed walk whose inner cycle follows its boundary**: the
faces on the walk's side, when the exterior face is on the other side.  The pocket's cycle is the
walk, and its complement's cycle is the reversed walk. -/
noncomputable def ofNoncrossingClosedWalkInner (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hin : (hw.innerCycle Delta.planar).FollowsBoundary) : PocketRegion Delta where
  faces := sideFaces Delta.toCombMap walk
  outside := sideOutside Delta.toCombMap walk
  mem_outside_iff := mem_sideOutside_iff Delta.toCombMap walk
  outerFace_mem := (mem_sideOutside_iff Delta.toCombMap walk _).mpr hout
  inner := (hw.innerCycle Delta.planar).toDiscRegion_of_followsBoundary Delta.toCombMap _ hin
    Delta.planar
  outer := hw.outerDiscRegion_of_innerFollows Delta.planar hin
  invDarts_outer_rotate := ⟨0, by
    rw [List.rotate_zero]
    exact invDarts_reverse_map_alpha walk⟩

theorem ofNoncrossingClosedWalkInner_faces (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hin : (hw.innerCycle Delta.planar).FollowsBoundary) :
    (ofNoncrossingClosedWalkInner hw hout hin).faces = sideFaces Delta.toCombMap walk :=
  rfl

theorem ofNoncrossingClosedWalkInner_inner_cycle
    (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hin : (hw.innerCycle Delta.planar).FollowsBoundary) :
    (ofNoncrossingClosedWalkInner hw hout hin).inner.cycle = walk :=
  rfl

theorem ofNoncrossingClosedWalkInner_outer_cycle
    (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hin : (hw.innerCycle Delta.planar).FollowsBoundary) :
    (ofNoncrossingClosedWalkInner hw hout hin).outer.cycle =
      walk.reverse.map Delta.toCombMap.alpha :=
  rfl

/-- The inverse complement cycle of the pocket is the walk. -/
theorem ofNoncrossingClosedWalkInner_invDarts_outer
    (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hin : (hw.innerCycle Delta.planar).FollowsBoundary) :
    Embedded.invDarts Delta (ofNoncrossingClosedWalkInner hw hout hin).outer.cycle = walk :=
  invDarts_reverse_map_alpha walk

end PocketRegion

namespace Surgery.InnerDiscRegion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} {walk : List Delta.toCombMap.Dart}

/-- **The collapsible disc region of a noncrossing walk whose inner cycle follows its boundary**,
when no relator cell lies on its side.  Its cycle is the walk. -/
noncomputable def ofNoncrossingClosedWalkInner (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hin : (hw.innerCycle Delta.planar).FollowsBoundary)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ sideFaces Delta.toCombMap walk) :
    InnerDiscRegion Delta :=
  ofPocketRegion (PocketRegion.ofNoncrossingClosedWalkInner hw hout hin) hcells

theorem ofNoncrossingClosedWalkInner_faces (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hin : (hw.innerCycle Delta.planar).FollowsBoundary)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ sideFaces Delta.toCombMap walk) :
    (ofNoncrossingClosedWalkInner hw hout hin hcells).faces = sideFaces Delta.toCombMap walk :=
  rfl

theorem ofNoncrossingClosedWalkInner_region_cycle
    (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hin : (hw.innerCycle Delta.planar).FollowsBoundary)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ sideFaces Delta.toCombMap walk) :
    (ofNoncrossingClosedWalkInner hw hout hin hcells).region.cycle = walk :=
  rfl

end Surgery.InnerDiscRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.followsBoundary_of_faces_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.reclosedMap_euler_of_faces_eq
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.exists_walkClass
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.sideFaces_reverseMapAlpha
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.sideOutside_reverseMapAlpha
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.reclosed_euler_outer_of_innerFollows
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.outerDiscRegion_of_innerFollows
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.ofNoncrossingClosedWalkInner
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.ofNoncrossingClosedWalkInner_invDarts_outer
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerDiscRegion.ofNoncrossingClosedWalkInner
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerDiscRegion.ofNoncrossingClosedWalkInner_region_cycle
