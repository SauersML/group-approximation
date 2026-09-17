import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Lobe
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Predicate
import GroupApproximation.Meta.AxiomGuard

/-!
# The rose step from a separated lobe

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  This module builds the pocket step of `P10ChordLift.RoseStepStatement`
from a closed lobe of the boundary cycle (module `P10Rose/Lobe`).

* `ofLobe`: a closed, duplicate-free sub-list `L` of the boundary cycle, with the relator cell
  `kept` in its lobe and an `s_1 t_1 s_2 t_2` decomposition, is a pocket face set.  The side norms
  are bounded by the side lengths through letter labels.
* `exists_step_of_cut`: a pocket in walk order whose cycle is `A ++ B ++ C`, where the cut sub-walk
  `B` is closed, starts at the vertex where the rest starts, and has at most `ε` darts, gives a
  pocket in walk order with proper arcs and strictly fewer repeated visits.  The relator cell lies
  in the lobe of `B` (take `B` alone with zero arcs) or in the lobe of `A ++ C` (take the rest
  with the arcs of `K`).
* `exists_step_of_firstSide_cut`, `exists_step_of_secondSide_cut`: the cut inside a side.

## The remaining gap

The endpoint `rose : P10ChordLift.RoseStepStatement` is not provided here.  The rose hypothesis
`AllNonFirstTurnsCrossed K` does not produce a closed sub-walk of a side: see the lake-rose
configuration in the docstring of `P10Rose/Lobe`.  The steps above need a closed cut `B`, which
the lake absorption `PocketFaceSet.absorb` would supply once it is shown to keep walk order.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides

/-- The empty arc at the base position of an arc. -/
def zeroArc {Dart : Type*} {cycle : List Dart} (a : CyclicArc cycle) : CyclicArc cycle where
  start := a.start
  length := 0
  length_le := Nat.zero_le _

section Steps

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- A pocket whose boundary cycle is a closed dart walk is in walk order. -/
theorem closedWalk_of_isClosedDartWalk (K : PocketFaceSet D eps X lo hi)
    (h : IsClosedDartWalk X.toCombMap K.boundary.cycle) : K.ClosedWalk := by
  obtain ⟨_, hc, hclose⟩ := h
  exact ⟨hc, hclose⟩

/-- **The pocket face set of a closed lobe.** -/
noncomputable def ofLobe (K : PocketFaceSet D eps X lo hi)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (L : List X.toCombMap.Dart) (hL : ∀ d ∈ L, d ∈ K.boundary.cycle)
    (hclosed : ∀ d ∈ L, ∀ e ∈ K.boundary.cycle,
      Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
        d e → e ∈ L)
    (hne : L ≠ []) (hnd : L.Nodup)
    (hkept : (cell X K.kept).face ∈ lobeFaces X.toCombMap K.boundary.cycle L)
    (t₁ : CyclicArc (cellDarts X K.source)) (t₂ : CyclicArc (outerDarts X))
    (s₁ s₂ : List X.toCombMap.Dart) (hdec : L = s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps) (hlo : lo ≤ t₂.start.1)
    (hhi : t₂.start.1 + t₂.length ≤ hi) : PocketFaceSet D eps X lo hi where
  faces := lobeFaces X.toCombMap K.boundary.cycle L
  outerFace_not_mem := fun h =>
    K.outerFace_not_mem (mem_faces_of_mem_lobeFaces K.boundary.cycle_mem_iff hL h)
  source := K.source
  source_not_mem := fun h =>
    K.source_not_mem (mem_faces_of_mem_lobeFaces K.boundary.cycle_mem_iff hL h)
  kept := K.kept
  kept_mem := hkept
  sourceArc := t₁
  targetArc := t₂
  firstSide := s₁
  secondSide := s₂
  boundary := lobeBoundary K.boundary.cycle_mem_iff hL hclosed hne hnd
  decomposition := hdec
  firstSide_length_le := hs₁
  secondSide_length_le := hs₂
  firstSide_norm_le := (PocketFaceSet.wordNorm_dartWord_le_length hlabel s₁).trans hs₁
  secondSide_norm_le := (PocketFaceSet.wordNorm_dartWord_le_length hlabel s₂).trans hs₂
  lo_le := hlo
  le_hi := hhi

/-- **The step from a closed cut of the boundary cycle.** -/
theorem exists_step_of_cut (K : PocketFaceSet D eps X lo hi)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) (hK : K.ClosedWalk)
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    {A B C : List X.toCombMap.Dart} (hc : K.boundary.cycle = A ++ (B ++ C)) (hB : B ≠ [])
    (hrest : C ++ A ≠ [])
    (hv : X.toCombMap.vertexOf (B.head hB) = X.toCombMap.vertexOf ((C ++ A).head hrest))
    (hclosed : ∀ d ∈ B, ∀ e ∈ K.boundary.cycle,
      Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
        d e → e ∈ B)
    (hBlen : B.length ≤ eps) {s₁ s₂ : List X.toCombMap.Dart}
    (hdec : A ++ C = s₁ ++ invDarts X K.sourceArc.darts ++ s₂ ++ K.targetArc.darts)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps) :
    ∃ K' : PocketFaceSet D eps X lo hi, K'.ClosedWalk ∧
      K'.sourceArc.length < (cellDarts X K'.source).length ∧
      K'.targetArc.length < (outerDarts X).length ∧ K'.repeatedVisits < K.repeatedVisits := by
  have hperm : List.Perm K.boundary.cycle (B ++ (A ++ C)) := by
    rw [hc]
    exact List.perm_append_comm_assoc _ _ _
  obtain ⟨hndB, hndL', -⟩ := List.nodup_append.mp (K.boundary.cycle_nodup.perm hperm)
  have hLB : ∀ d ∈ B, d ∈ K.boundary.cycle := fun d hd =>
    hperm.mem_iff.mpr (List.mem_append_left _ hd)
  have hL' : ∀ d ∈ A ++ C, d ∈ K.boundary.cycle := fun d hd =>
    hperm.mem_iff.mpr (List.mem_append_right _ hd)
  have hy : (C ++ A).head hrest ∈ A ++ C :=
    List.perm_append_comm.mem_iff.mp (List.head_mem hrest)
  have hw0 : IsClosedDartWalk X.toCombMap (A ++ (B ++ C)) := by
    rw [← hc]
    exact ⟨K.boundary.cycle_nonempty, hK.1, hK.2⟩
  have hw1 : IsClosedDartWalk X.toCombMap (B ++ (C ++ A)) := by
    have h := hw0.append_comm
    rwa [List.append_assoc] at h
  obtain ⟨hwB, hwR⟩ := closedDartWalk_split hw1 hB hrest hv
  rcases mem_lobeFaces_or X.planar.1 K.boundary.cycle_mem_iff K.boundary.cycle_nonempty hperm
    K.kept_mem with hkB | hkL'
  · have hdecB : B = B ++ invDarts X (zeroArc K.sourceArc).darts ++ [] ++
        (zeroArc K.targetArc).darts := by
      show B = B ++ [] ++ [] ++ []
      simp only [List.append_nil]
    have hhi : (zeroArc K.targetArc).start.1 + (zeroArc K.targetArc).length ≤ hi := by
      have h := K.le_hi
      show K.targetArc.start.1 + 0 ≤ hi
      omega
    refine ⟨ofLobe K hlabel B hLB hclosed hB hndB hkB (zeroArc K.sourceArc) (zeroArc K.targetArc)
      B [] hdecB hBlen (Nat.zero_le _) K.lo_le hhi, closedWalk_of_isClosedDartWalk _ hwB,
      Nat.lt_of_le_of_lt (Nat.zero_le _) hsrc, Nat.lt_of_le_of_lt (Nat.zero_le _) htgt, ?_⟩
    unfold PocketFaceSet.repeatedVisits
    exact length_sub_card_lt X.toCombMap.vertexOf hperm (List.head_mem hB) hy hv
  · have hwL' : IsClosedDartWalk X.toCombMap (A ++ C) := hwR.append_comm
    refine ⟨ofLobe K hlabel (A ++ C) hL' (closed_right hperm K.boundary.cycle_nodup hclosed)
      (List.ne_nil_of_mem hy) hndL' hkL' K.sourceArc K.targetArc s₁ s₂ hdec hs₁ hs₂ K.lo_le
      K.le_hi, closedWalk_of_isClosedDartWalk _ hwL', hsrc, htgt, ?_⟩
    unfold PocketFaceSet.repeatedVisits
    exact length_sub_card_lt X.toCombMap.vertexOf (hperm.trans List.perm_append_comm) hy
      (List.head_mem hB) hv.symm

/-- **The step from a closed cut inside the first side.** -/
theorem exists_step_of_firstSide_cut (K : PocketFaceSet D eps X lo hi)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) (hK : K.ClosedWalk)
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    {p B q : List X.toCombMap.Dart} (hfirst : K.firstSide = p ++ B ++ q) (hB : B ≠ [])
    (hrest : q ++ (invDarts X K.sourceArc.darts ++ (K.secondSide ++ K.targetArc.darts)) ++ p ≠ [])
    (hv : X.toCombMap.vertexOf (B.head hB) = X.toCombMap.vertexOf
      ((q ++ (invDarts X K.sourceArc.darts ++ (K.secondSide ++ K.targetArc.darts)) ++ p).head
        hrest))
    (hclosed : ∀ d ∈ B, ∀ e ∈ K.boundary.cycle,
      Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
        d e → e ∈ B) :
    ∃ K' : PocketFaceSet D eps X lo hi, K'.ClosedWalk ∧
      K'.sourceArc.length < (cellDarts X K'.source).length ∧
      K'.targetArc.length < (outerDarts X).length ∧ K'.repeatedVisits < K.repeatedVisits := by
  have hlen := K.firstSide_length_le
  rw [hfirst, List.length_append, List.length_append] at hlen
  refine exists_step_of_cut K hlabel hK hsrc htgt (A := p) (B := B)
    (C := q ++ (invDarts X K.sourceArc.darts ++ (K.secondSide ++ K.targetArc.darts)))
    (s₁ := p ++ q) (s₂ := K.secondSide) ?_ hB hrest hv hclosed (by omega) ?_
    (by rw [List.length_append]; omega) K.secondSide_length_le
  · rw [K.decomposition, hfirst]
    simp only [List.append_assoc]
  · simp only [List.append_assoc]

/-- **The step from a closed cut inside the second side.** -/
theorem exists_step_of_secondSide_cut (K : PocketFaceSet D eps X lo hi)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) (hK : K.ClosedWalk)
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    {p B q : List X.toCombMap.Dart} (hsecond : K.secondSide = p ++ B ++ q) (hB : B ≠ [])
    (hrest : q ++ K.targetArc.darts ++ (K.firstSide ++ (invDarts X K.sourceArc.darts ++ p)) ≠ [])
    (hv : X.toCombMap.vertexOf (B.head hB) = X.toCombMap.vertexOf
      ((q ++ K.targetArc.darts ++ (K.firstSide ++ (invDarts X K.sourceArc.darts ++ p))).head
        hrest))
    (hclosed : ∀ d ∈ B, ∀ e ∈ K.boundary.cycle,
      Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
        d e → e ∈ B) :
    ∃ K' : PocketFaceSet D eps X lo hi, K'.ClosedWalk ∧
      K'.sourceArc.length < (cellDarts X K'.source).length ∧
      K'.targetArc.length < (outerDarts X).length ∧ K'.repeatedVisits < K.repeatedVisits := by
  have hlen := K.secondSide_length_le
  rw [hsecond, List.length_append, List.length_append] at hlen
  refine exists_step_of_cut K hlabel hK hsrc htgt
    (A := K.firstSide ++ (invDarts X K.sourceArc.darts ++ p)) (B := B)
    (C := q ++ K.targetArc.darts) (s₁ := K.firstSide) (s₂ := p ++ q) ?_ hB hrest hv hclosed
    (by omega) ?_ K.firstSide_length_le (by rw [List.length_append]; omega)
  · rw [K.decomposition, hsecond]
    simp only [List.append_assoc]
  · simp only [List.append_assoc]

end Steps

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.zeroArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.closedWalk_of_isClosedDartWalk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.ofLobe
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.exists_step_of_cut
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.exists_step_of_firstSide_cut
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.exists_step_of_secondSide_cut
