import GroupApproximation.GGT.VanKampen.FaceSetBoundaryWalk

/-!
# The peeled cycle carries exactly the erased boundary

When a planar ear is peeled, the boundary cycle `before ++ arc ++ after` is
replaced by `before ++ invDarts interior ++ after`, where `arc ++ interior` is
the boundary of the peeled face read from the start of the arc.  Two of the
fields of the new `FaceSetBoundary` record are settled here with no planarity
input beyond the ear condition itself: the new word enumerates exactly the
boundary darts of the erased face set, and it has no repetitions.

The ear condition used is the honest one: every dart of the current cycle
lying on the peeled face is already in the arc, so the face meets the cycle in
that one arc.  The peeled face is also assumed unpinched, that is no edge
carries it on both sides.  Without that assumption the interior of the face
contains `alpha`-pairs of its own, and their reverses are not boundary darts of
the erased set, so the peeled word above is simply the wrong list.

What is still missing for the full record is the walk structure: that the new
word is a `BoundaryStep` chain and closes.  Determinism pins the chain once it
is known that the new word is a single cycle, which is the remaining planar
content, together with the existence of the ear.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

open GroupApproximation.HullSC

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

noncomputable local instance faceDecidableEqPeeledCycle :
    DecidableEq Delta.toCombMap.Face := Classical.decEq _

section Peel

variable {faces : Finset Delta.toCombMap.Face}
  {face : Delta.toCombMap.Face}
  {before arc after interior : List Delta.toCombMap.Dart} {k : ℕ}

/-! ## Reading off the two blocks -/

/-- The darts of the peeled face are exactly the darts of `arc ++ interior`. -/
theorem faceOf_eq_iff_mem_arc_append
    (hfacerot : (Delta.faceBoundary face).darts.rotate k = arc ++ interior)
    (x : Delta.toCombMap.Dart) :
    x ∈ arc ++ interior ↔ Delta.toCombMap.faceOf x = face := by
  rw [← hfacerot, List.mem_rotate]
  exact (Delta.faceBoundary face).mem_iff x

/-- The arc and the interior of the peeled face are disjoint and duplicate
free. -/
theorem nodup_arc_append_interior
    (hfacerot : (Delta.faceBoundary face).darts.rotate k = arc ++ interior) :
    (arc ++ interior).Nodup := by
  rw [← hfacerot]
  exact List.nodup_rotate.mpr (Delta.faceBoundary face).nodup

/-- Every dart of the current cycle outside the arc is a boundary dart which
does not lie on the peeled face. -/
theorem isBoundaryDart_of_mem_before_after
    (boundary : FaceSetBoundary Delta faces)
    (hcycle : boundary.cycle = before ++ arc ++ after)
    (hear : ∀ d ∈ boundary.cycle,
      Delta.toCombMap.faceOf d = face → d ∈ arc)
    {x : Delta.toCombMap.Dart} (hx : x ∈ before ∨ x ∈ after) :
    IsBoundaryDart Delta faces x ∧ Delta.toCombMap.faceOf x ≠ face := by
  have hcycNodup : (before ++ arc ++ after).Nodup := by
    rw [← hcycle]
    exact boundary.cycle_nodup
  obtain ⟨hnodupBA, _, hdisjBAafter⟩ := List.nodup_append.mp hcycNodup
  obtain ⟨_, _, hdisjBarc⟩ := List.nodup_append.mp hnodupBA
  have hxC : x ∈ boundary.cycle := by
    rw [hcycle]
    rcases hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_left _ hx)
    · exact List.mem_append_right _ hx
  refine ⟨(boundary.cycle_mem_iff x).1 hxC, ?_⟩
  intro hxf
  have hxarc : x ∈ arc := hear x hxC hxf
  rcases hx with hx | hx
  · exact hdisjBarc x hx x hxarc rfl
  · exact hdisjBAafter x (List.mem_append_right _ hxarc) x hx rfl

/-- Every dart of the interior of the peeled face has its reverse based in a
selected face other than the peeled one.  The arc carries all the boundary
darts of the face, so an interior dart faces into the region, and unpinchedness
puts it in a different face. -/
theorem faceOf_alpha_of_mem_interior
    (boundary : FaceSetBoundary Delta faces)
    (hfacemem : face ∈ faces)
    (hfacerot : (Delta.faceBoundary face).darts.rotate k = arc ++ interior)
    (hself : ∀ y : Delta.toCombMap.Dart,
      Delta.toCombMap.faceOf y = face →
        Delta.toCombMap.faceOf (Delta.toCombMap.alpha y) ≠ face)
    (hear : ∀ d ∈ boundary.cycle,
      Delta.toCombMap.faceOf d = face → d ∈ arc)
    {y : Delta.toCombMap.Dart} (hy : y ∈ interior) :
    Delta.toCombMap.faceOf y = face ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha y) ∈ faces ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha y) ≠ face := by
  have hyface : Delta.toCombMap.faceOf y = face :=
    (faceOf_eq_iff_mem_arc_append hfacerot y).1 (List.mem_append_right _ hy)
  refine ⟨hyface, ?_, hself y hyface⟩
  by_contra hcon
  have hB : IsBoundaryDart Delta faces y := ⟨by rw [hyface]; exact hfacemem, hcon⟩
  have hC : y ∈ boundary.cycle := (boundary.cycle_mem_iff y).2 hB
  have harc : y ∈ arc := hear y hC hyface
  obtain ⟨_, _, hdisj⟩ := List.nodup_append.mp (nodup_arc_append_interior hfacerot)
  exact hdisj y harc y hy rfl

/-! ## The peeled word enumerates the erased boundary -/

/-- The peeled word contains exactly the boundary darts of the erased face
set. -/
theorem mem_peeled_iff
    (boundary : FaceSetBoundary Delta faces)
    (hfacemem : face ∈ faces)
    (hcycle : boundary.cycle = before ++ arc ++ after)
    (hfacerot : (Delta.faceBoundary face).darts.rotate k = arc ++ interior)
    (hself : ∀ y : Delta.toCombMap.Dart,
      Delta.toCombMap.faceOf y = face →
        Delta.toCombMap.faceOf (Delta.toCombMap.alpha y) ≠ face)
    (hear : ∀ d ∈ boundary.cycle,
      Delta.toCombMap.faceOf d = face → d ∈ arc)
    (d : Delta.toCombMap.Dart) :
    d ∈ before ++ invDarts Delta interior ++ after ↔
      IsBoundaryDart Delta (faces.erase face) d := by
  constructor
  · intro hd
    rcases List.mem_append.mp hd with hd | hd
    · rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨hb, hne⟩ :=
          isBoundaryDart_of_mem_before_after boundary hcycle hear (Or.inl hd)
        exact isBoundaryDart_erase_of_isBoundaryDart hb hne
      · have hai : Delta.toCombMap.alpha d ∈ interior :=
          (mem_invDarts_iff interior d).1 hd
        obtain ⟨haf, hamem, hane⟩ :=
          faceOf_alpha_of_mem_interior boundary hfacemem hfacerot hself hear hai
        rw [Delta.toCombMap.alpha_involutive] at hamem hane
        rw [isBoundaryDart_erase_iff]
        exact ⟨hamem, hane, Or.inr haf⟩
    · obtain ⟨hb, hne⟩ :=
        isBoundaryDart_of_mem_before_after boundary hcycle hear (Or.inr hd)
      exact isBoundaryDart_erase_of_isBoundaryDart hb hne
  · intro hd
    rw [isBoundaryDart_erase_iff] at hd
    obtain ⟨hdmem, hdne, hcase⟩ := hd
    rcases hcase with hcase | hcase
    · have hB : IsBoundaryDart Delta faces d := ⟨hdmem, hcase⟩
      have hC : d ∈ boundary.cycle := (boundary.cycle_mem_iff d).2 hB
      rw [hcycle] at hC
      rcases List.mem_append.mp hC with hC | hC
      · rcases List.mem_append.mp hC with hC | hC
        · exact List.mem_append_left _ (List.mem_append_left _ hC)
        · exact absurd
            ((faceOf_eq_iff_mem_arc_append hfacerot d).1
              (List.mem_append_left _ hC)) hdne
      · exact List.mem_append_right _ hC
    · have hai : Delta.toCombMap.alpha d ∈ arc ++ interior :=
        (faceOf_eq_iff_mem_arc_append hfacerot (Delta.toCombMap.alpha d)).2 hcase
      have hnotarc : Delta.toCombMap.alpha d ∉ arc := by
        intro harc
        have hC : Delta.toCombMap.alpha d ∈ boundary.cycle := by
          rw [hcycle]
          exact List.mem_append_left _ (List.mem_append_right _ harc)
        have hB := (boundary.cycle_mem_iff (Delta.toCombMap.alpha d)).1 hC
        have hnot := hB.2
        rw [Delta.toCombMap.alpha_involutive] at hnot
        exact hnot hdmem
      have hint : Delta.toCombMap.alpha d ∈ interior := by
        rcases List.mem_append.mp hai with h | h
        · exact absurd h hnotarc
        · exact h
      exact List.mem_append_left _
        (List.mem_append_right _ ((mem_invDarts_iff interior d).2 hint))

/-! ## The peeled word has no repetitions -/

/-- The peeled word is duplicate free. -/
theorem nodup_peeled
    (boundary : FaceSetBoundary Delta faces)
    (hfacemem : face ∈ faces)
    (hcycle : boundary.cycle = before ++ arc ++ after)
    (hfacerot : (Delta.faceBoundary face).darts.rotate k = arc ++ interior)
    (hself : ∀ y : Delta.toCombMap.Dart,
      Delta.toCombMap.faceOf y = face →
        Delta.toCombMap.faceOf (Delta.toCombMap.alpha y) ≠ face)
    (hear : ∀ d ∈ boundary.cycle,
      Delta.toCombMap.faceOf d = face → d ∈ arc) :
    (before ++ invDarts Delta interior ++ after).Nodup := by
  have hcycNodup : (before ++ arc ++ after).Nodup := by
    rw [← hcycle]
    exact boundary.cycle_nodup
  obtain ⟨hnodupBA, hnodupAfter, hdisjBAafter⟩ := List.nodup_append.mp hcycNodup
  obtain ⟨hnodupBefore, _, _⟩ := List.nodup_append.mp hnodupBA
  obtain ⟨_, hnodupInterior, _⟩ :=
    List.nodup_append.mp (nodup_arc_append_interior hfacerot)
  -- a dart of the peeled word coming from the interior faces the peeled face
  have hinv : ∀ x : Delta.toCombMap.Dart, x ∈ invDarts Delta interior →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha x) = face := by
    intro x hx
    obtain ⟨hxf, _, _⟩ :=
      faceOf_alpha_of_mem_interior boundary hfacemem hfacerot hself hear
        ((mem_invDarts_iff interior x).1 hx)
    exact hxf
  -- a dart of the old cycle outside the arc never faces the peeled face
  have hout : ∀ x : Delta.toCombMap.Dart, x ∈ before ∨ x ∈ after →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha x) ≠ face := by
    intro x hx hxf
    obtain ⟨hb, _⟩ :=
      isBoundaryDart_of_mem_before_after boundary hcycle hear hx
    apply hb.2
    rw [hxf]
    exact hfacemem
  have hdisjBefore : ∀ a ∈ before, ∀ b ∈ invDarts Delta interior, a ≠ b := by
    intro x hxb y hyi hxy
    refine hout x (Or.inl hxb) ?_
    rw [hxy]
    exact hinv y hyi
  have hdisjAfter : ∀ a ∈ invDarts Delta interior, ∀ b ∈ after, a ≠ b := by
    intro x hxi y hya hxy
    refine hout y (Or.inr hya) ?_
    rw [← hxy]
    exact hinv x hxi
  have hleft : (before ++ invDarts Delta interior).Nodup := by
    refine List.nodup_append.mpr ⟨hnodupBefore, ?_, hdisjBefore⟩
    exact invDarts_nodup hnodupInterior
  refine List.nodup_append.mpr ⟨hleft, hnodupAfter, ?_⟩
  intro x hx y hy hxy
  rcases List.mem_append.mp hx with hx | hx
  · exact hdisjBAafter x (List.mem_append_left _ hx) y hy hxy
  · exact hdisjAfter x hx y hy hxy

end Peel

end Embedded
end VanKampen
end GGT
end GroupApproximation
