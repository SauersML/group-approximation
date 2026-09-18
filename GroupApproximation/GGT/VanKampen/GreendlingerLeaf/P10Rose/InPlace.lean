import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Cut
import GroupApproximation.Meta.AxiomGuard

/-!
# In-place pocket steps: arbitrary face sets, non-contiguous lobes, filled lakes

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  The rose step (`RoseCombinatorialStepStatement`, module `P10Rose/Cut`)
never needs to change the diagram: every move replaces the face set `K.faces` inside the same
diagram `X`.  This module packages the three constructors of such moves, each ending in the common
conclusion "a pocket face set of `X` in walk order, with proper arcs and strictly fewer repeated
visits".  The lemmas are stated for an arbitrary `PocketFaceSet`, so the sibling leaf
(`Piece06`, cell rose step) can import them.

## Plan of the combinatorics

Write `c = K.boundary.cycle` and `F = K.faces`.

* **Counting.**  If `c ~ L ++ R`, the new cycle is `L`, and some `x ∈ L` and `y ∈ R` start at one
  vertex, then `|L| - #vert L < |c| - #vert c` (`length_sub_card_lt`): the vertex set of `c` is the
  union of those of `L` and `R`, which meet.  This is `repeatedVisits_lt_of_perm`.
* **Any face set (`ofFaces`, `step_of_faces`).**  A face set `F'` avoiding the exterior face and
  the source cell, containing the kept cell, and a duplicate-free list
  `L = s₁ ++ t₁⁻¹ ++ s₂ ++ t₂` listing exactly the boundary darts of `F'`, with `|s_i| ≤ ε` and the
  arc `t₂` between `lo` and `hi`, is a pocket face set (letter labels bound the side norms by the
  side lengths).  If `L` is a closed walk, the arcs are proper and `c ~ L ++ R` with a shared vertex,
  this is a step.
* **Non-contiguous lobes (`step_of_lobe`).**  This generalises `exists_step_of_cut`: instead of a
  contiguous cut `A ++ (B ++ C)` take any split `c ~ B ++ L` into two closed walks, with `B` closed
  under the face relation `FaceClassStep (walkKeep c)`, `|B| ≤ ε`, and `L` decomposed around any
  proper arcs `t₁ ⊆ ∂(source)` and `t₂ ⊆ ∂X` between `lo` and `hi` (sub-arcs are allowed).  The
  relator cell lies in the lobe of `B` or in the lobe of `L` (`mem_lobeFaces_or`); in the first
  case `B` with empty arcs is the step, in the second `L` with the arcs `t₁`, `t₂`.
* **Filled lakes (`step_of_absorb`).**  When the source cell faces the exterior piece of the
  complement of `F`, `PocketFaceSet.absorb` fills every lake; if its cycle
  `s₁ ++ t₁⁻¹ ++ s₂ ++ t₂` (with `s_i ⊆` the old sides) is a closed walk and some filled dart shares
  a vertex with a kept dart, this is a step.

## Why the gap is stated in place, and not as "a lobe or all lakes"

A disc `F` with two holes `L_s` (containing the source cell) and `L_2`, whose three boundary
circles meet at one vertex `w` and nowhere else, with the passages at `w` in the crossed order
`a ↦ a - 1`, satisfies every hypothesis of the rose step: `w` is visited three times, the three
turns at `w` are non-first and crossed, all other turns are first.  There `F` is a single class of
the face relation, so no proper lobe exists, and `absorb` does not apply (the source cell lies in a
lake).  The step fills `L_2` alone: `F ∪ L_2` has boundary the outer circle followed by the circle
of `L_s`, a closed walk through `w` twice, obtained by deleting the circle of `L_2` from `c`
(a sub-walk from `w` to `w`), which keeps the arcs and shortens `s₁` or `s₂`.  This move is
`step_of_faces` with `F' = F ∪ L_2`.  Hence the remaining gap (`RoseInPlaceStepStatement`, module
`P10Rose/Proof`) asks for an in-place step, whose proof must choose `F'` (remove some classes of `F`
not containing the kept cell, or fill some lakes other than the lake of the source cell) and order
its boundary darts into a closed walk around the arcs.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides

section InPlace

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Fewer repeated visits from a split cycle.**  If the old cycle is a permutation of the new
cycle followed by a list `R`, and some new dart shares its vertex with a dart of `R`, the repeated
visits drop strictly. -/
theorem repeatedVisits_lt_of_perm (K K' : PocketFaceSet D eps X lo hi)
    {R : List X.toCombMap.Dart} (hperm : List.Perm K.boundary.cycle (K'.boundary.cycle ++ R))
    {x y : X.toCombMap.Dart} (hx : x ∈ K'.boundary.cycle) (hy : y ∈ R)
    (hxy : X.toCombMap.vertexOf x = X.toCombMap.vertexOf y) :
    K'.repeatedVisits < K.repeatedVisits := by
  unfold PocketFaceSet.repeatedVisits
  exact length_sub_card_lt X.toCombMap.vertexOf hperm hx hy hxy

/-- **The pocket face set of an arbitrary face set** listed as `s₁ ++ t₁⁻¹ ++ s₂ ++ t₂`. -/
noncomputable def ofFaces (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (faces : Finset X.toCombMap.Face) (hout : X.outerFace ∉ faces)
    (source kept : Fin X.rCellCount) (hsource : (cell X source).face ∉ faces)
    (hkept : (cell X kept).face ∈ faces)
    (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
    (s₁ s₂ : List X.toCombMap.Dart)
    (hne : s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts ≠ [])
    (hnd : (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts).Nodup)
    (hmem : ∀ d, d ∈ s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts ↔
      IsBoundaryDart X.toCombMap faces d)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps) (hlo : lo ≤ t₂.start.1)
    (hhi : t₂.start.1 + t₂.length ≤ hi) : PocketFaceSet D eps X lo hi where
  faces := faces
  outerFace_not_mem := hout
  source := source
  source_not_mem := hsource
  kept := kept
  kept_mem := hkept
  sourceArc := t₁
  targetArc := t₂
  firstSide := s₁
  secondSide := s₂
  boundary :=
    { cycle := s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts
      cycle_nonempty := hne
      cycle_nodup := hnd
      cycle_mem_iff := hmem }
  decomposition := rfl
  firstSide_length_le := hs₁
  secondSide_length_le := hs₂
  firstSide_norm_le := (PocketFaceSet.wordNorm_dartWord_le_length hlabel s₁).trans hs₁
  secondSide_norm_le := (PocketFaceSet.wordNorm_dartWord_le_length hlabel s₂).trans hs₂
  lo_le := hlo
  le_hi := hhi

/-- **The step from an arbitrary face set** whose boundary, listed as `s₁ ++ t₁⁻¹ ++ s₂ ++ t₂`, is a
closed walk with proper arcs and a sub-list of the old cycle sharing a vertex with the rest. -/
theorem step_of_faces (K : PocketFaceSet D eps X lo hi)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {faces : Finset X.toCombMap.Face} (hout : X.outerFace ∉ faces)
    {source kept : Fin X.rCellCount} (hsource : (cell X source).face ∉ faces)
    (hkept : (cell X kept).face ∈ faces)
    {t₁ : CyclicArc (cellDarts X source)} {t₂ : CyclicArc (outerDarts X)}
    {s₁ s₂ : List X.toCombMap.Dart}
    (hmem : ∀ d, d ∈ s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts ↔
      IsBoundaryDart X.toCombMap faces d)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps) (hlo : lo ≤ t₂.start.1)
    (hhi : t₂.start.1 + t₂.length ≤ hi)
    (ht₁ : t₁.length < (cellDarts X source).length) (ht₂ : t₂.length < (outerDarts X).length)
    (hwalk : IsClosedDartWalk X.toCombMap (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts))
    {R : List X.toCombMap.Dart}
    (hperm : List.Perm K.boundary.cycle ((s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts) ++ R))
    {x y : X.toCombMap.Dart} (hx : x ∈ s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts) (hy : y ∈ R)
    (hxy : X.toCombMap.vertexOf x = X.toCombMap.vertexOf y) :
    ∃ K' : PocketFaceSet D eps X lo hi, K'.ClosedWalk ∧
      K'.sourceArc.length < (cellDarts X K'.source).length ∧
      K'.targetArc.length < (outerDarts X).length ∧ K'.repeatedVisits < K.repeatedVisits := by
  have hnd : (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts).Nodup :=
    (List.nodup_append.mp (K.boundary.cycle_nodup.perm hperm)).1
  refine ⟨ofFaces hlabel faces hout source kept hsource hkept t₁ t₂ s₁ s₂ (List.ne_nil_of_mem hx)
    hnd hmem hs₁ hs₂ hlo hhi, ?_, ht₁, ht₂, ?_⟩
  · exact closedWalk_of_isClosedDartWalk _ hwalk
  · refine repeatedVisits_lt_of_perm K _ ?_ ?_ hy hxy
    · exact hperm
    · exact hx

/-- **The step from a split of the cycle into two closed walks**, one of them closed under the
face relation and no longer than `ε`, the other around proper (sub-)arcs.  This generalises
`exists_step_of_cut` to non-contiguous lobes and to sub-arcs. -/
theorem step_of_lobe (K : PocketFaceSet D eps X lo hi)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {B L : List X.toCombMap.Dart} (hperm : List.Perm K.boundary.cycle (B ++ L))
    {x y : X.toCombMap.Dart} (hx : x ∈ B) (hy : y ∈ L)
    (hxy : X.toCombMap.vertexOf x = X.toCombMap.vertexOf y)
    (hwB : IsClosedDartWalk X.toCombMap B) (hwL : IsClosedDartWalk X.toCombMap L)
    (hclosed : ∀ d ∈ B, ∀ e ∈ K.boundary.cycle,
      Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
        d e → e ∈ B)
    (hBlen : B.length ≤ eps)
    {t₁ : CyclicArc (cellDarts X K.source)} {t₂ : CyclicArc (outerDarts X)}
    {s₁ s₂ : List X.toCombMap.Dart} (hdec : L = s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps) (hlo : lo ≤ t₂.start.1)
    (hhi : t₂.start.1 + t₂.length ≤ hi)
    (ht₁ : t₁.length < (cellDarts X K.source).length) (ht₂ : t₂.length < (outerDarts X).length) :
    ∃ K' : PocketFaceSet D eps X lo hi, K'.ClosedWalk ∧
      K'.sourceArc.length < (cellDarts X K'.source).length ∧
      K'.targetArc.length < (outerDarts X).length ∧ K'.repeatedVisits < K.repeatedVisits := by
  obtain ⟨hndB, hndL, -⟩ := List.nodup_append.mp (K.boundary.cycle_nodup.perm hperm)
  have hLB : ∀ d ∈ B, d ∈ K.boundary.cycle := fun d hd =>
    hperm.mem_iff.mpr (List.mem_append_left _ hd)
  have hLL : ∀ d ∈ L, d ∈ K.boundary.cycle := fun d hd =>
    hperm.mem_iff.mpr (List.mem_append_right _ hd)
  rcases mem_lobeFaces_or X.planar.1 K.boundary.cycle_mem_iff K.boundary.cycle_nonempty hperm
    K.kept_mem with hkB | hkL
  · have hdecB : B = B ++ invDarts X (zeroArc K.sourceArc).darts ++ [] ++
        (zeroArc K.targetArc).darts := by
      show B = B ++ [] ++ [] ++ []
      simp only [List.append_nil]
    have hhiB : (zeroArc K.targetArc).start.1 + (zeroArc K.targetArc).length ≤ hi := by
      have h := K.le_hi
      show K.targetArc.start.1 + 0 ≤ hi
      omega
    refine ⟨ofLobe K hlabel B hLB hclosed (List.ne_nil_of_mem hx) hndB hkB (zeroArc K.sourceArc)
      (zeroArc K.targetArc) B [] hdecB hBlen (Nat.zero_le _) K.lo_le hhiB, ?_,
      Nat.lt_of_le_of_lt (Nat.zero_le _) ht₁, Nat.lt_of_le_of_lt (Nat.zero_le _) ht₂, ?_⟩
    · exact closedWalk_of_isClosedDartWalk _ hwB
    · unfold PocketFaceSet.repeatedVisits
      exact length_sub_card_lt X.toCombMap.vertexOf hperm hx hy hxy
  · refine ⟨ofLobe K hlabel L hLL (closed_right hperm K.boundary.cycle_nodup hclosed)
      (List.ne_nil_of_mem hy) hndL hkL t₁ t₂ s₁ s₂ hdec hs₁ hs₂ hlo hhi, ?_, ht₁, ht₂, ?_⟩
    · exact closedWalk_of_isClosedDartWalk _ hwL
    · unfold PocketFaceSet.repeatedVisits
      exact length_sub_card_lt X.toCombMap.vertexOf (hperm.trans List.perm_append_comm) hy hx
        hxy.symm

/-- **The step from filling all lakes**, when the source cell faces the exterior piece, the filled
cycle is a closed walk, and a filled dart shares a vertex with a kept dart. -/
theorem step_of_absorb (K : PocketFaceSet D eps X lo hi)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    (hsource : (cell X K.source).face ∈
      ExteriorComponent.component X.toCombMap K.faces X.outerFace)
    {s₁ s₂ : List X.toCombMap.Dart} (hs₁ : s₁ ⊆ K.firstSide) (hs₂ : s₂ ⊆ K.secondSide)
    (hmem : ∀ d, d ∈ s₁ ++ invDarts X K.sourceArc.darts ++ s₂ ++ K.targetArc.darts ↔
      IsBoundaryDart X.toCombMap K.faces d ∧
        X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
          ExteriorComponent.component X.toCombMap K.faces X.outerFace)
    (hwalk : IsClosedDartWalk X.toCombMap
      (s₁ ++ invDarts X K.sourceArc.darts ++ s₂ ++ K.targetArc.darts))
    {R : List X.toCombMap.Dart}
    (hperm : List.Perm K.boundary.cycle
      ((s₁ ++ invDarts X K.sourceArc.darts ++ s₂ ++ K.targetArc.darts) ++ R))
    {x y : X.toCombMap.Dart}
    (hx : x ∈ s₁ ++ invDarts X K.sourceArc.darts ++ s₂ ++ K.targetArc.darts) (hy : y ∈ R)
    (hxy : X.toCombMap.vertexOf x = X.toCombMap.vertexOf y) :
    ∃ K' : PocketFaceSet D eps X lo hi, K'.ClosedWalk ∧
      K'.sourceArc.length < (cellDarts X K'.source).length ∧
      K'.targetArc.length < (outerDarts X).length ∧ K'.repeatedVisits < K.repeatedVisits := by
  have hnd : (s₁ ++ invDarts X K.sourceArc.darts ++ s₂ ++ K.targetArc.darts).Nodup :=
    (List.nodup_append.mp (K.boundary.cycle_nodup.perm hperm)).1
  refine ⟨K.absorb hlabel hsource s₁ s₂ hs₁ hs₂ (List.ne_nil_of_mem hx) hnd hmem, ?_, hsrc, htgt,
    ?_⟩
  · exact closedWalk_of_isClosedDartWalk _ hwalk
  · refine repeatedVisits_lt_of_perm K _ ?_ ?_ hy hxy
    · exact hperm
    · exact hx

end InPlace

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.repeatedVisits_lt_of_perm
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.ofFaces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.step_of_faces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.step_of_lobe
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.step_of_absorb
