import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchStep
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeAbsorption
import GroupApproximation.Meta.AxiomGuard

/-!
# Trimming an arc of a pocket into a side

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  A pocket face set whose source arc or target arc is full is never
simple (`Estimating/OsinPocketFullArc.lean`), and surgery that carries arcs and sides keeps a full
arc full.  The boundary cycle of a pocket face set can be split in more than one way.  When a side
is shorter than the side bound `ε`, one dart of an arc next to that side moves into the side.  The
face set and its cycle are unchanged, so walk order, the repeated visits and simplicity are
unchanged, and the arc loses one dart.  Letter labels bound the norm of the longer side by its
length.

* `CyclicArc.dropLastArc` and `CyclicArc.tailArc`: an arc less its last dart, and less its first.
* `PocketFaceSet.trimSourceLast`: the first dart of the reversed source arc joins the first side.
* `PocketFaceSet.trimTargetHead`: the first dart of the target arc joins the second side.
* `closedWalk_trimSourceLast`, `repeatedVisits_trimSourceLast`, `simple_trimSourceLast_iff`, and
  the same for `trimTargetHead`.
* `trimSourceLast_sourceArc_lt` and `trimTargetHead_targetArc_lt`: the trimmed arc is not full.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

namespace Embedded.CyclicArc

variable {α : Type*} {cycle : List α}

/-- The arc with the same start and one dart fewer. -/
def dropLastArc (arc : CyclicArc cycle) : CyclicArc cycle where
  start := arc.start
  length := arc.length - 1
  length_le := (Nat.sub_le _ _).trans arc.length_le

/-- The arc starting one position later, with one dart fewer. -/
def tailArc (arc : CyclicArc cycle) (hs : arc.start.1 < cycle.length) : CyclicArc cycle where
  start := ⟨arc.start.1 + 1, by omega⟩
  length := arc.length - 1
  length_le := (Nat.sub_le _ _).trans arc.length_le

theorem dropLastArc_darts (arc : CyclicArc cycle) : arc.dropLastArc.darts = arc.darts.dropLast := by
  show arc.rotated.take (arc.length - 1) = arc.darts.dropLast
  rw [CyclicArc.darts, List.dropLast_eq_take, List.take_take, List.length_take, arc.rotated_length,
    Nat.min_eq_left arc.length_le, Nat.min_eq_left (Nat.sub_le _ _)]

theorem tailArc_darts (arc : CyclicArc cycle) (hs : arc.start.1 < cycle.length) :
    (arc.tailArc hs).darts = arc.darts.tail := by
  have h1 : (arc.tailArc hs).darts = (cycle.rotate (arc.start.1 + 1)).take (arc.length - 1) :=
    congrArg (List.take (arc.length - 1)) (arc.tailArc hs).rotated_eq_rotate
  have h2 : arc.darts = (cycle.rotate arc.start.1).take arc.length :=
    congrArg (List.take arc.length) arc.rotated_eq_rotate
  have hle := arc.length_le
  have hne : cycle.rotate arc.start.1 ≠ [] := by
    intro h
    have hl := congrArg List.length h
    rw [List.length_rotate, List.length_nil] at hl
    omega
  obtain ⟨a, L, hL⟩ := List.exists_cons_of_ne_nil hne
  have hLlen : L.length + 1 = cycle.length := by
    have hl := congrArg List.length hL
    rw [List.length_rotate, List.length_cons] at hl
    omega
  have hrot1 : (a :: L).rotate 1 = L ++ [a] := (List.rotate_cons_succ L a 0).trans (List.rotate_zero _)
  rw [h1, h2, ← List.rotate_rotate, hL, hrot1, List.take_append_of_le_length (by omega)]
  rcases Nat.eq_zero_or_pos arc.length with h0 | hpos
  · rw [h0]
    rfl
  · obtain ⟨m, hm⟩ : ∃ m, arc.length = m + 1 := ⟨arc.length - 1, by omega⟩
    rw [hm, List.take_succ_cons, List.tail_cons, Nat.add_sub_cancel]

end Embedded.CyclicArc

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- The reversed arc starts with the reversal of the last dart of the arc. -/
theorem invDarts_eq_getLast_cons {t : List X.toCombMap.Dart} (hne : t ≠ []) :
    invDarts X t = X.toCombMap.alpha (t.getLast hne) :: invDarts X t.dropLast := by
  obtain ⟨L, z, rfl⟩ : ∃ L z, t = L ++ [z] :=
    ⟨t.dropLast, t.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  rw [List.getLast_concat, List.dropLast_concat]
  show (L ++ [z]).reverse.map X.toCombMap.alpha = X.toCombMap.alpha z :: L.reverse.map X.toCombMap.alpha
  rw [List.reverse_append, List.map_append]
  rfl

/-- **Trim the source arc into the first side.**  The first dart of the reversed source arc, the
reversal of the last dart of the source arc, joins the first side, when the first side is shorter
than `ε`. -/
noncomputable def trimSourceLast (K : PocketFaceSet D eps X lo hi)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (hne : K.sourceArc.darts ≠ []) (hroom : K.firstSide.length < eps) :
    PocketFaceSet D eps X lo hi where
  faces := K.faces
  outerFace_not_mem := K.outerFace_not_mem
  source := K.source
  source_not_mem := K.source_not_mem
  kept := K.kept
  kept_mem := K.kept_mem
  sourceArc := K.sourceArc.dropLastArc
  targetArc := K.targetArc
  firstSide := K.firstSide ++ [X.toCombMap.alpha (K.sourceArc.darts.getLast hne)]
  secondSide := K.secondSide
  boundary := K.boundary
  decomposition := by
    rw [K.decomposition, CyclicArc.dropLastArc_darts, invDarts_eq_getLast_cons hne]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  firstSide_length_le := by
    rw [List.length_append, List.length_singleton]
    omega
  secondSide_length_le := K.secondSide_length_le
  firstSide_norm_le := (wordNorm_dartWord_le_length hlabel _).trans (by
    rw [List.length_append, List.length_singleton]
    omega)
  secondSide_norm_le := K.secondSide_norm_le
  lo_le := K.lo_le
  le_hi := K.le_hi

/-- **Trim the target arc into the second side.**  The first dart of the target arc joins the
second side, when the second side is shorter than `ε` and the arc does not start at the wrapped
position. -/
noncomputable def trimTargetHead (K : PocketFaceSet D eps X lo hi)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (hne : K.targetArc.darts ≠ []) (hs : K.targetArc.start.1 < (outerDarts X).length)
    (hroom : K.secondSide.length < eps) : PocketFaceSet D eps X lo hi where
  faces := K.faces
  outerFace_not_mem := K.outerFace_not_mem
  source := K.source
  source_not_mem := K.source_not_mem
  kept := K.kept
  kept_mem := K.kept_mem
  sourceArc := K.sourceArc
  targetArc := K.targetArc.tailArc hs
  firstSide := K.firstSide
  secondSide := K.secondSide ++ [K.targetArc.darts.head hne]
  boundary := K.boundary
  decomposition := by
    rw [K.decomposition, CyclicArc.tailArc_darts]
    conv_lhs => rw [← List.cons_head_tail hne]
    simp only [List.append_assoc, List.singleton_append]
  firstSide_length_le := K.firstSide_length_le
  secondSide_length_le := by
    rw [List.length_append, List.length_singleton]
    omega
  firstSide_norm_le := K.firstSide_norm_le
  secondSide_norm_le := (wordNorm_dartWord_le_length hlabel _).trans (by
    rw [List.length_append, List.length_singleton]
    omega)
  lo_le := Nat.le_succ_of_le K.lo_le
  le_hi := by
    have h1 := K.le_hi
    have h2 : 0 < K.targetArc.length := by
      rw [← CyclicArc.darts_length]
      exact List.length_pos_iff.mpr hne
    show K.targetArc.start.1 + 1 + (K.targetArc.length - 1) ≤ hi
    omega

section Trim

variable (K : PocketFaceSet D eps X lo hi)
  (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))

theorem closedWalk_trimSourceLast (hne : K.sourceArc.darts ≠ []) (hroom : K.firstSide.length < eps)
    (hK : K.ClosedWalk) : (K.trimSourceLast hlabel hne hroom).ClosedWalk :=
  hK

theorem repeatedVisits_trimSourceLast (hne : K.sourceArc.darts ≠ [])
    (hroom : K.firstSide.length < eps) :
    (K.trimSourceLast hlabel hne hroom).repeatedVisits = K.repeatedVisits :=
  rfl

theorem simple_trimSourceLast_iff (hne : K.sourceArc.darts ≠ []) (hroom : K.firstSide.length < eps) :
    (K.trimSourceLast hlabel hne hroom).Simple ↔ K.Simple :=
  Iff.rfl

/-- The trimmed source arc is shorter than the source cell. -/
theorem trimSourceLast_sourceArc_lt (hne : K.sourceArc.darts ≠ []) (hroom : K.firstSide.length < eps) :
    (K.trimSourceLast hlabel hne hroom).sourceArc.length < (cellDarts X K.source).length := by
  have h1 := K.sourceArc.length_le
  have h2 : 0 < K.sourceArc.length := by
    rw [← CyclicArc.darts_length]
    exact List.length_pos_iff.mpr hne
  show K.sourceArc.length - 1 < (cellDarts X K.source).length
  omega

theorem closedWalk_trimTargetHead (hne : K.targetArc.darts ≠ [])
    (hs : K.targetArc.start.1 < (outerDarts X).length) (hroom : K.secondSide.length < eps)
    (hK : K.ClosedWalk) : (K.trimTargetHead hlabel hne hs hroom).ClosedWalk :=
  hK

theorem repeatedVisits_trimTargetHead (hne : K.targetArc.darts ≠ [])
    (hs : K.targetArc.start.1 < (outerDarts X).length) (hroom : K.secondSide.length < eps) :
    (K.trimTargetHead hlabel hne hs hroom).repeatedVisits = K.repeatedVisits :=
  rfl

theorem simple_trimTargetHead_iff (hne : K.targetArc.darts ≠ [])
    (hs : K.targetArc.start.1 < (outerDarts X).length) (hroom : K.secondSide.length < eps) :
    (K.trimTargetHead hlabel hne hs hroom).Simple ↔ K.Simple :=
  Iff.rfl

/-- The trimmed target arc is shorter than the exterior cycle. -/
theorem trimTargetHead_targetArc_lt (hne : K.targetArc.darts ≠ [])
    (hs : K.targetArc.start.1 < (outerDarts X).length) (hroom : K.secondSide.length < eps) :
    (K.trimTargetHead hlabel hne hs hroom).targetArc.length < (outerDarts X).length := by
  have h1 := K.targetArc.length_le
  have h2 : 0 < K.targetArc.length := by
    rw [← CyclicArc.darts_length]
    exact List.length_pos_iff.mpr hne
  show K.targetArc.length - 1 < (outerDarts X).length
  omega

end Trim

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.dropLastArc_darts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.tailArc_darts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.trimSourceLast
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.trimTargetHead
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.simple_trimSourceLast_iff
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.trimSourceLast_sourceArc_lt
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.trimTargetHead_targetArc_lt
