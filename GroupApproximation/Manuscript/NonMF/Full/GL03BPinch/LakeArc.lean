import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillWalk
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryRotation
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Arcs of the cell pocket walk on the lake-filled outer walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex 2134, Hull's small cancellation theorem, through Osin's Lemma 9.7).

The piece of the exterior face off the side of the pocket walk `K = s₁ t₁⁻¹ s₂ t₂⁻¹` is the
exterior piece.  Filling every other face (the lakes) gives an enclosed face set turning to
successors, over the outer walk `lakeWalk` (`LakeFill.lakeWalk_enclosedFaceSetSucc`).  This file
reads that outer walk against `K`.
* `pocketWalk_mem_iff`: a dart of `K` is on a side or reverses an arc dart.
* `lakeWalk_length_le_of_lakes`: when both cells are lakes, the outer walk reverses side darts
  only, so it has at most `2ε` darts.
* `exists_lakeWalk_arc`: when the cell of an arc is in the exterior piece, the outer walk started
  at its first dart reads the arc, then at most as many darts as the sides.
* `emptyArc`: the empty arc of a cycle.

These re-prove, without the unfinished `P07LakeExclusion.Proof` in their import closure, the
helpers of the foreign `P07LakeExclusion/LakeFillArc.lean`.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex 2134); certifies no printed sentence on its
own.
-/

namespace GroupApproximation.Full.GL03BPinch

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.ExteriorComponent
open GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill

/-- A list of length at most `n + n` splits into two lists of length at most `n` (`thm:hull`). -/
theorem exists_split_two {α : Type*} {l : List α} {n : ℕ} (h : l.length ≤ n + n) :
    ∃ s₁ s₂ : List α, s₁.length ≤ n ∧ s₂.length ≤ n ∧ l = s₁ ++ s₂ :=
  ⟨l.take n, l.drop n, List.length_take_le n l, by rw [List.length_drop]; omega,
    (List.take_append_drop n l).symm⟩

/-- **The empty arc of a cycle** (`thm:hull`). -/
def emptyArc {Dart : Type v} (cycle : List Dart) : CyclicArc cycle :=
  ⟨0, 0, Nat.zero_le _⟩

theorem emptyArc_darts {Dart : Type v} (cycle : List Dart) : (emptyArc cycle).darts = [] :=
  rfl

theorem emptyArc_length {Dart : Type v} (cycle : List Dart) : (emptyArc cycle).length = 0 :=
  rfl

section Map

variable {M : CombMap.{v}}

/-- Duplicate-free darts whose reverses lie on a list are at most as many as that list
(`thm:hull`). -/
theorem length_le_of_forall_alpha_mem {l s : List M.Dart} (hl : l.Nodup)
    (h : ∀ r ∈ l, M.alpha r ∈ s) : l.length ≤ s.length := by
  have hsub : l.map M.alpha ⊆ s := by
    intro d hd
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hd
    exact h r hr
  have hle := (List.subperm_of_subset (hl.map M.alpha.injective) hsub).length_le
  rwa [List.length_map] at hle

variable {wk : List M.Dart}

/-- **A face chain on the outer walk is its start** (`thm:hull`).  A duplicate-free face chain of
darts of the outer walk of `x₀`, starting at `x₀`, is a prefix of that outer walk. -/
theorem lakeWalk_eq_append_drop (hw : IsNoncrossingClosedWalk M wk) (hM : M.IsPlanar)
    {o : M.Face} (hout : o ∉ sideFaces M wk) {x₀ : (walkMap M wk).Dart}
    (hx₀ : M.faceOf x₀.1 ∈ component M (sideFaces M wk) o) {l : List M.Dart} (hl : l.Nodup)
    (hc : l.IsChain fun d e => M.facePerm d = e) (hmem : ∀ d ∈ l, d ∈ lakeWalk M wk x₀)
    (h0 : 0 < l.length) (hx : x₀.1 = l[0]'h0) :
    lakeWalk M wk x₀ = l ++ (lakeWalk M wk x₀).drop l.length := by
  have hsub : l ⊆ lakeWalk M wk x₀ := by
    intro d hd
    exact hmem d hd
  have hle : l.length ≤ (lakeWalk M wk x₀).length := (List.subperm_of_subset hl hsub).length_le
  have hkeep : ∀ d ∈ l, walkKeep M wk d := fun d hd =>
    Or.inr ((mem_lakeWalk_iff hw hM hout hx₀ d).mp (hmem d hd)).1
  have htake : (lakeWalk M wk x₀).take l.length = l := by
    apply List.ext_getElem
    · rw [List.length_take, Nat.min_eq_left hle]
    · intro n _ h₂
      rw [List.getElem_take, getElem_lakeWalk]
      exact walkMap_facePerm_pow_getElem hc hkeep h0 hx n h₂
  have h := List.take_append_drop l.length (lakeWalk M wk x₀)
  rw [htake] at h
  exact h.symm

end Map

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- The inverse of a concatenation is the concatenation of the inverses in reverse order
(`thm:hull`). -/
theorem pinch_invDarts_append (a b : List X.toCombMap.Dart) :
    invDarts X (a ++ b) = invDarts X b ++ invDarts X a := by
  simp only [invDarts, List.reverse_append, List.map_append]

/-- A dart of an arc of a cell lies on that cell (`thm:hull`). -/
theorem arcFaceOf_eq {k : Fin X.rCellCount} (A : CyclicArc (cellDarts X k))
    {x : X.toCombMap.Dart} (hx : x ∈ A.darts) : X.toCombMap.faceOf x = (cell X k).face :=
  ((X.faceBoundary (cell X k).face).mem_iff x).mp (A.mem_cycle_of_mem_darts hx)

theorem arcFaceOf_mem {k : Fin X.rCellCount} (A : CyclicArc (cellDarts X k))
    {C : Finset X.toCombMap.Face} (hk : (cell X k).face ∈ C) {x : X.toCombMap.Dart}
    (hx : x ∈ A.darts) : X.toCombMap.faceOf x ∈ C := by
  rw [arcFaceOf_eq A hx]
  exact hk

theorem not_mem_arc_of_faceOf {k : Fin X.rCellCount} (A : CyclicArc (cellDarts X k))
    {C : Finset X.toCombMap.Face} {r : X.toCombMap.Dart} (hr : X.toCombMap.faceOf r ∈ C)
    (hk : (cell X k).face ∉ C) : r ∉ A.darts := fun hrA => by
  rw [arcFaceOf_eq A hrA] at hr
  exact hk hr

/-- Consecutive darts of an arc follow the face permutation (`thm:hull`). -/
theorem arc_isChain_facePerm {k : Fin X.rCellCount} (A : CyclicArc (cellDarts X k)) :
    A.darts.IsChain fun d e => X.toCombMap.facePerm d = e := by
  rw [CyclicArc.darts, CyclicArc.rotated_eq_rotate]
  exact (isChain_rotate_of_isChain_closes (X.faceBoundary (cell X k).face).nonempty
    (X.faceBoundary (cell X k).face).chain (X.faceBoundary (cell X k).face).closes _).take _

/-- The darts of the pocket walk `s₁ t₁⁻¹ s₂ t₂⁻¹` (`thm:hull`). -/
theorem pocketWalk_mem_iff (K : CellPocketWalk D eps X i j) (y : X.toCombMap.Dart) :
    y ∈ K.walk ↔ y ∈ K.firstSide ∨ (∃ x ∈ K.firstArc.darts, X.toCombMap.alpha x = y) ∨
      y ∈ K.secondSide ∨ ∃ x ∈ K.secondArc.darts, X.toCombMap.alpha x = y := by
  simp only [CellPocketWalk.walk, invDarts, List.mem_append, List.mem_map, List.mem_reverse,
    or_assoc]

theorem alpha_mem_walk_firstArc (K : CellPocketWalk D eps X i j) {x : X.toCombMap.Dart}
    (hx : x ∈ K.firstArc.darts) : X.toCombMap.alpha x ∈ K.walk :=
  (pocketWalk_mem_iff K _).mpr (Or.inr (Or.inl ⟨x, hx, rfl⟩))

theorem alpha_mem_walk_secondArc (K : CellPocketWalk D eps X i j) {x : X.toCombMap.Dart}
    (hx : x ∈ K.secondArc.darts) : X.toCombMap.alpha x ∈ K.walk :=
  (pocketWalk_mem_iff K _).mpr (Or.inr (Or.inr (Or.inr ⟨x, hx, rfl⟩)))

/-- A walk dart reversing no arc dart reverses a side dart (`thm:hull`). -/
theorem alpha_mem_sides (K : CellPocketWalk D eps X i j) {r : X.toCombMap.Dart}
    (hr : X.toCombMap.alpha r ∈ K.walk) (h1 : r ∉ K.firstArc.darts)
    (h2 : r ∉ K.secondArc.darts) : X.toCombMap.alpha r ∈ K.firstSide ++ K.secondSide := by
  rw [List.mem_append]
  rcases (pocketWalk_mem_iff K _).mp hr with h | ⟨x, hx, hxr⟩ | h | ⟨x, hx, hxr⟩
  · exact Or.inl h
  · obtain rfl := X.toCombMap.alpha.injective hxr
    exact absurd hx h1
  · exact Or.inr h
  · obtain rfl := X.toCombMap.alpha.injective hxr
    exact absurd hx h2

/-- Darts at most as many as the sides give at most `2ε` inverse darts (`thm:hull`). -/
theorem invDarts_length_le_sides (K : CellPocketWalk D eps X i j) {R : List X.toCombMap.Dart}
    (hR : R.length ≤ (K.firstSide ++ K.secondSide).length) :
    (invDarts X R).length ≤ eps + eps := by
  have h1 := K.firstSide_length_le
  have h2 := K.secondSide_length_le
  simp only [invDarts, List.length_map, List.length_reverse]
  rw [List.length_append] at hR
  omega

/-- A face on the side of a walk is off the exterior piece (`thm:hull`). -/
theorem not_mem_component_of_mem_sideFaces {wk : List X.toCombMap.Dart}
    (hout : X.outerFace ∉ sideFaces X.toCombMap wk) {f : X.toCombMap.Face}
    (hf : f ∈ sideFaces X.toCombMap wk) :
    f ∉ component X.toCombMap (sideFaces X.toCombMap wk) X.outerFace := fun hc =>
  not_mem_of_mem_component hout hc hf

/-- **The outer walk when both cells are lakes** (`thm:hull`).  If neither cell of the pocket walk
is in the exterior piece, the outer walk from a dart facing that piece reverses side darts only,
so it has at most `2ε` darts. -/
theorem lakeWalk_length_le_of_lakes (K : CellPocketWalk D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hi : (cell X i).face ∉ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    (hj : (cell X j).face ∉ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    {x₀ : (walkMap X.toCombMap K.walk).Dart}
    (hx₀ : X.toCombMap.faceOf x₀.1 ∈
      component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace) :
    (invDarts X (lakeWalk X.toCombMap K.walk x₀)).length ≤ eps + eps := by
  refine invDarts_length_le_sides K
    (length_le_of_forall_alpha_mem (lakeWalk_nodup x₀) fun r hr => ?_)
  obtain ⟨hα, hc⟩ := (mem_lakeWalk_iff hw X.planar hout hx₀ r).mp hr
  exact alpha_mem_sides K hα (not_mem_arc_of_faceOf K.firstArc hc hi)
    (not_mem_arc_of_faceOf K.secondArc hc hj)

/-- **A dart facing the exterior piece** (`thm:hull`): the outer walk has a start dart. -/
theorem exists_start (K : CellPocketWalk D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk) :
    ∃ x₀ : (walkMap X.toCombMap K.walk).Dart, X.toCombMap.faceOf x₀.1 ∈
      component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace := by
  obtain ⟨d, hα, hc⟩ := exists_alpha_mem_component hw X.planar hout
  exact ⟨⟨d, Or.inr hα⟩, hc⟩

/-- **The outer walk from an arc** (`thm:hull`).  If the cell of an arc is in the exterior piece
and the arc darts face the walk, the outer walk from the first arc dart reads the arc, then darts
off the arc whose reverses are forced into `s`. -/
theorem lakeWalk_arc {wk : List X.toCombMap.Dart} (hw : IsNoncrossingClosedWalk X.toCombMap wk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap wk) {k : Fin X.rCellCount}
    (A : CyclicArc (cellDarts X k)) (h0 : 0 < A.darts.length)
    (hAwk : ∀ x ∈ A.darts, X.toCombMap.alpha x ∈ wk)
    (hk : (cell X k).face ∈ component X.toCombMap (sideFaces X.toCombMap wk) X.outerFace)
    {x₀ : (walkMap X.toCombMap wk).Dart} (hx : x₀.1 = A.darts[0]'h0) {s : List X.toCombMap.Dart}
    (hs : ∀ r, X.toCombMap.alpha r ∈ wk →
      X.toCombMap.faceOf r ∈ component X.toCombMap (sideFaces X.toCombMap wk) X.outerFace →
      r ∉ A.darts → X.toCombMap.alpha r ∈ s) :
    ∃ R : List X.toCombMap.Dart,
      lakeWalk X.toCombMap wk x₀ = A.darts ++ R ∧ R.length ≤ s.length := by
  have hx₀ : X.toCombMap.faceOf x₀.1 ∈
      component X.toCombMap (sideFaces X.toCombMap wk) X.outerFace := by
    rw [hx]
    exact arcFaceOf_mem A hk (List.getElem_mem h0)
  have hmem : ∀ d ∈ A.darts, d ∈ lakeWalk X.toCombMap wk x₀ := fun d hd =>
    (mem_lakeWalk_iff hw X.planar hout hx₀ d).mpr ⟨hAwk d hd, arcFaceOf_mem A hk hd⟩
  have hL := lakeWalk_eq_append_drop hw X.planar hout hx₀ (A.darts_nodup (cellDarts_nodup X k))
    (arc_isChain_facePerm A) hmem h0 hx
  refine ⟨(lakeWalk X.toCombMap wk x₀).drop A.darts.length, hL, ?_⟩
  have hnd : (A.darts ++ (lakeWalk X.toCombMap wk x₀).drop A.darts.length).Nodup := by
    rw [← hL]
    exact lakeWalk_nodup x₀
  refine length_le_of_forall_alpha_mem (List.nodup_append.mp hnd).2.1 fun r hr => ?_
  have hrL : r ∈ lakeWalk X.toCombMap wk x₀ := by
    rw [hL]
    exact List.mem_append.mpr (Or.inr hr)
  obtain ⟨hα, hc⟩ := (mem_lakeWalk_iff hw X.planar hout hx₀ r).mp hrL
  exact hs r hα hc fun hrA => (List.nodup_append.mp hnd).2.2 r hrA r hr rfl

/-- **The outer walk from an arc**, with its start dart chosen (`thm:hull`). -/
theorem exists_lakeWalk_arc {wk : List X.toCombMap.Dart}
    (hw : IsNoncrossingClosedWalk X.toCombMap wk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap wk) {k : Fin X.rCellCount}
    (A : CyclicArc (cellDarts X k)) (hApos : 0 < A.length)
    (hAwk : ∀ x ∈ A.darts, X.toCombMap.alpha x ∈ wk)
    (hk : (cell X k).face ∈ component X.toCombMap (sideFaces X.toCombMap wk) X.outerFace)
    {s : List X.toCombMap.Dart}
    (hs : ∀ r, X.toCombMap.alpha r ∈ wk →
      X.toCombMap.faceOf r ∈ component X.toCombMap (sideFaces X.toCombMap wk) X.outerFace →
      r ∉ A.darts → X.toCombMap.alpha r ∈ s) :
    ∃ (x₀ : (walkMap X.toCombMap wk).Dart) (R : List X.toCombMap.Dart),
      X.toCombMap.faceOf x₀.1 ∈ component X.toCombMap (sideFaces X.toCombMap wk) X.outerFace ∧
        lakeWalk X.toCombMap wk x₀ = A.darts ++ R ∧ R.length ≤ s.length := by
  have h0 : 0 < A.darts.length := by
    rw [A.darts_length]
    exact hApos
  obtain ⟨R, hL, hR⟩ := lakeWalk_arc hw hout A h0 hAwk hk
    (x₀ := ⟨A.darts[0]'h0, Or.inr (hAwk _ (List.getElem_mem h0))⟩) rfl hs
  exact ⟨⟨A.darts[0]'h0, Or.inr (hAwk _ (List.getElem_mem h0))⟩, R,
    arcFaceOf_mem A hk (List.getElem_mem h0), hL, hR⟩

end GroupApproximation.Full.GL03BPinch

#audit_axioms GroupApproximation.Full.GL03BPinch.exists_split_two
#audit_axioms GroupApproximation.Full.GL03BPinch.emptyArc_darts
#audit_axioms GroupApproximation.Full.GL03BPinch.length_le_of_forall_alpha_mem
#audit_axioms GroupApproximation.Full.GL03BPinch.lakeWalk_eq_append_drop
#audit_axioms GroupApproximation.Full.GL03BPinch.lakeWalk_length_le_of_lakes
#audit_axioms GroupApproximation.Full.GL03BPinch.exists_start
#audit_axioms GroupApproximation.Full.GL03BPinch.exists_lakeWalk_arc
