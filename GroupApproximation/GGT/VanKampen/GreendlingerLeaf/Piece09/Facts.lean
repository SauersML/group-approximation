import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkColour
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCopyWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketInnerWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkChain
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.Walk
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.Boundary
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 09: facts on regions, arcs and cut boundary cycles

Steps 2 to 4 of the proof in `GreendlingerLeaf/Piece09/Walk.lean`.

* `region_cycle_eq`: the boundary cycle of a region to the outer boundary reads
  `t_x⁻¹ r_x u_x l_x`, with the target arc read forwards.
* `region_mem_iff`, `region_dartPath`: that cycle lists the boundary darts of the region and is
  a closed dart path.
* `darts_eq_append_drop`: an arc with the same start and fewer darts lists a prefix of the darts.
* `not_iff_iff_walkKeep`: the colouring hypothesis of `PocketWalkColour.mem_iff_of_faceSetBoundary`
  from a list of boundary darts.
* `closed_cut`: replacing a shared stretch `Mid` of two closed paths `A Mid B` and `Mid L` by `L⁻¹`
  leaves a closed path `A L⁻¹ B`.
* `exists_cut_of_split`: the boundary cycle of the difference of two face sets.
* `exists_dartPath_of_closedWalk`: a pocket face set in walk order is a closed dart path.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09

universe u w v

open Embedded SimpleClosedWalkSides

section Region

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}

/-- On the exterior target, the boundary darts of the target arc are its darts. -/
theorem targetBoundaryDarts_of_none {target : Option (Fin X.rCellCount)}
    (arc : CyclicArc (targetDarts X target)) (ht : target = none) :
    targetBoundaryDarts X target arc = arc.darts := by
  subst ht
  rfl

/-- **The boundary cycle of a region to the outer boundary.** -/
theorem region_cycle_eq (x : RegionCandidate D eps X) (hxt : x.2.target = none) :
    x.2.boundary.cycle =
      invDarts X x.2.sourceArc.darts ++ x.2.rightSide ++ x.2.targetArc.darts ++ x.2.leftSide := by
  have h := x.2.boundary_decomposition
  rw [targetBoundaryDarts_of_none x.2.targetArc hxt] at h
  exact h

/-- The boundary darts of a region to the outer boundary. -/
theorem region_mem_iff (x : RegionCandidate D eps X) (hxt : x.2.target = none) :
    ∀ d, d ∈ invDarts X x.2.sourceArc.darts ++ x.2.rightSide ++ x.2.targetArc.darts ++
        x.2.leftSide ↔
      X.toCombMap.faceOf d ∈ x.1 ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ x.1 := by
  intro d
  rw [← region_cycle_eq x hxt]
  exact x.2.boundary.cycle_mem_iff d

/-- The boundary cycle of a region to the outer boundary is a closed dart path. -/
theorem region_dartPath (x : RegionCandidate D eps X) (hxt : x.2.target = none) :
    ∃ q, DartPath X.toCombMap q q
      (invDarts X x.2.sourceArc.darts ++ x.2.rightSide ++ x.2.targetArc.darts ++ x.2.leftSide) := by
  have h : ∃ q, DartPath X.toCombMap q q x.2.boundary.cycle :=
    ⟨_, dartPath_of_isChain_closes X.toCombMap x.2.boundary.cycle x.2.boundary.cycle_nonempty
      x.2.boundary.isChain_closes⟩
  rwa [region_cycle_eq x hxt] at h

/-- A pocket face set in walk order is a closed dart path. -/
theorem exists_dartPath_of_closedWalk {lo hi : ℕ} (P : PocketFaceSet D eps X lo hi)
    (hP : P.ClosedWalk) : ∃ p, DartPath X.toCombMap p p P.boundary.cycle := by
  obtain ⟨hchain, hclose⟩ := hP
  have h := dartPath_of_isChain X.toCombMap P.boundary.cycle P.boundary.cycle_nonempty hchain
  rw [hclose] at h
  exact ⟨_, h⟩

end Region

/-- **A prefix arc.**  An arc with the same start as `T` and at most as many darts lists the first
darts of `T`. -/
theorem darts_eq_append_drop {α : Type*} {cycle : List α} (T T' : CyclicArc cycle)
    (hs : T'.start.1 = T.start.1) (hl : T'.length ≤ T.length) :
    T.darts = T'.darts ++ T.darts.drop T'.length := by
  have h : T.darts.take T'.length = T'.darts := by
    show (T.rotated.take T.length).take T'.length = T'.rotated.take T'.length
    rw [List.take_take, Nat.min_eq_left hl, CyclicArc.rotated_eq_rotate,
      CyclicArc.rotated_eq_rotate, hs]
  have h2 := List.take_append_drop T'.length T.darts
  rw [h] at h2
  exact h2.symm

/-- The colouring hypothesis from a list of boundary darts: a dart crosses the boundary of `faces`
exactly when it or its reverse lies on the list. -/
theorem not_iff_iff_walkKeep {M : CombMap.{u}} {w : List M.Dart} {faces : Finset M.Face}
    (h : ∀ d, d ∈ w ↔ M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces) (d : M.Dart) :
    ¬ (M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces) ↔ walkKeep M w d := by
  show _ ↔ d ∈ w ∨ M.alpha d ∈ w
  rw [h d, h (M.alpha d), M.alpha_involutive d]
  tauto

/-- **Cutting a closed path.**  If `A Mid B` and `Mid L` are closed paths and `Mid` is nonempty, then
`A L⁻¹ B` is a closed path. -/
theorem closed_cut {M : CombMap.{u}} {A Mid B L : List M.Dart}
    (hP : ∃ p, DartPath M p p (A ++ Mid ++ B)) (hR : ∃ q, DartPath M q q (Mid ++ L))
    (hMid : Mid ≠ []) : ∃ p, DartPath M p p (A ++ L.reverse.map M.alpha ++ B) := by
  obtain ⟨p, hp⟩ := hP
  obtain ⟨q, hq⟩ := hR
  obtain ⟨c₂, hAM, hB⟩ := (dartPath_append M (A ++ Mid) B p p).mp hp
  obtain ⟨c₁, hA, hM⟩ := (dartPath_append M A Mid p c₂).mp hAM
  obtain ⟨c₃, hM', hL⟩ := (dartPath_append M Mid L q q).mp hq
  obtain ⟨h₁, h₂⟩ := dartPath_unique M hM hM' hMid
  have hL' := dartPath_reverse_map M L c₃ q hL
  subst h₁
  subst h₂
  exact ⟨p, dartPath_append3 M hA hL' hB⟩

/-- **The boundary cycle of a difference of face sets.**  If the boundary cycle of `Pf` is
`A Mid B`, the boundary darts of `Rx ⊆ Pf` are those of `Mid L`, no dart of `L` lies on the cycle
of `Pf`, and `B` is nonempty, then `A L⁻¹ B` is a boundary cycle of `Pf \ Rx`. -/
theorem exists_cut_of_split {M : CombMap.{u}} [DecidableEq M.Face] {Pf Rx : Finset M.Face}
    (Pb : Surgery.MapCollapse.BoundaryCycle M Pf) {w A Mid B L : List M.Dart}
    (hPw : Pb.cycle = w) (hsplit : w = A ++ Mid ++ B)
    (h3 : ∀ d, d ∈ Mid ++ L ↔ M.faceOf d ∈ Rx ∧ M.faceOf (M.alpha d) ∉ Rx)
    (hL : L.Nodup) (h4 : Rx ⊆ Pf) (h5 : ∀ l ∈ L, l ∉ w) (hne : B ≠ []) :
    ∃ Bc : Surgery.MapCollapse.BoundaryCycle M (Pf \ Rx),
      Bc.cycle = A ++ L.reverse.map M.alpha ++ B := by
  subst hsplit
  have h1 : ∀ d, d ∈ A ++ Mid ++ B ↔ M.faceOf d ∈ Pf ∧ M.faceOf (M.alpha d) ∉ Pf := fun d => by
    rw [← hPw]
    exact Pb.cycle_mem_iff d
  have h2 : (A ++ Mid ++ B).Nodup := by
    rw [← hPw]
    exact Pb.cycle_nodup
  exact ⟨⟨A ++ L.reverse.map M.alpha ++ B, List.append_ne_nil_of_right_ne_nil _ hne,
    cut_nodup h1 h2 hL (fun l hl => ((h3 l).mp (List.mem_append_right Mid hl)).1) h4,
    fun d => cut_mem_iff h1 h2 h3 h4 h5 d⟩, rfl⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.targetBoundaryDarts_of_none
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.region_cycle_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.region_mem_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.region_dartPath
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.darts_eq_append_drop
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.not_iff_iff_walkKeep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.closed_cut
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.exists_cut_of_split
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.exists_dartPath_of_closedWalk
