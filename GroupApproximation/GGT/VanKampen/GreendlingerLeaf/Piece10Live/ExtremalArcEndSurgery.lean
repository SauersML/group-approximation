import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalArcEndDescent
import GroupApproximation.Meta.AxiomGuard

/-!
# The arc-end surgery rule: an extra exterior class, else a side class

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-26.

**LOUD: the targets `P10ExtremalRegion.ExtremalArcEndDescentKRKStatement` and
`P10ExtremalRegion.ExtremalArcEndDescentRKRStatement` (`Piece10Live/ExtremalArcEndDescent`, lane
gl-p10-22) are NOT closed here.**  Both are reduced, with proofs, to the single open
`ExtremalArcEndSurgeryStatement`, which names an explicit replacement class `r'`.

## The rule for `r'`

An *extra exterior class* (`ExtremalArcEndSurgeryExtraOut K z`) is a dart `z` with face outside
`K.faces` whose face class of `walkKeep K.boundary.cycle` avoids the exterior face and the source
face.  (In the plane model: a region outside the pocket walk other than the exterior region and
the source region.)  The rule:

* (A) if an extra exterior class exists, take `r'` to be any of them;
* (B) otherwise take `r'` to be a side dart (a dart of `K.firstSide ++ K.secondSide`) whose class
  is a choice class removing no arc dart.

## Proved here (no gap)

* `extremalArcEndSurgery_mem_faces_iff`: a face class lies on one side of `K.faces` (crossing an
  edge off the walk keeps the side, since a boundary dart lies on the walk);
* `extremalArcEndSurgery_removed_eq_zero`: an extra exterior class removes no arc dart (arc darts
  have their face in `K.faces` and the far face exterior or source);
* `extremalArcEndSurgery_choice`: an extra exterior class is a choice class
  (`ExtremalClassChoice`, avoiding the kept cell `K.kept` because that face is in `K.faces`);
* `extremalArcEndSurgery_removed_pos_of_krk`, `extremalArcEndSurgery_removed_pos_of_rkr`: each
  pattern removes an arc dart, so the count of `r` is positive and every class of count `0`
  strictly lowers it;
* `extremalArcEndSurgery_descent`: the rule `ExtremalArcEndSurgeryRule K` and a positive count
  give a linked choice class of smaller count;
* the endpoints `extremalArcEndSurgery_krk_of_surgery`, `extremalArcEndSurgery_rkr_of_surgery`,
  and the chain consequences `extremalArcEndSurgery_descent_of_surgery`,
  `extremalArcEndSurgery_extremalJordan_of_surgery`.

## The one open Statement

`ExtremalArcEndSurgeryStatement`: under the premises of the two targets, if some linked choice
class meets an arc in the pattern kept / removed / kept or removed / kept / removed, then
`ExtremalArcEndSurgeryRule K` holds: (A) every extra exterior class has linked removed runs
(`ExtremalMinimalLinkedRuns`); (B) if no extra exterior class exists, some side dart's class is a
choice class of count `0`, and every such side class has linked removed runs.

## LOUD: logical strength

`ExtremalArcEndSurgeryStatement` is logically STRONGER than each of the two targets: it implies
both (`extremalArcEndSurgery_krk_of_surgery`, `extremalArcEndSurgery_rkr_of_surgery`) and is not
implied by them, nor by `ExtremalArcEndDescentStatement`: it asserts that specific classes are
linked, and it gives count `0`, not only a smaller count.  It is strictly smaller in proof
content: the choice of `r'`, the choice property and count `0` of an extra exterior class, and
the strict drop of the count are proved.  What remains is planar: linked removed runs of the
chosen class, and in case (B) the existence of a suitable side class.

## Truth check (lane gl-p10-26, model of lanes gl-p10-14 / gl-p10-17 / gl-p10-21)

Scripts `explore2.py`, `explore3.py`, `explore4.py` in the scratchpad folder `gl-p10-26/`, run
on the enumerations of gl-p10-21 (pocket boundary as a plane Eulerian closed walk with a rotation
system, every instance of source arc, target arc, source region and exterior region, every
candidate class), at most 6 darts (6717858 instances):

* kept / removed / kept: 35610 hypotheses.  In 32198 an extra exterior region exists, and in all
  32198 EVERY extra exterior region is a linked choice class of count `0` (clause (A)).  In the
  other 3412 (2596 of them with source region equal to exterior region) some side region is a
  linked choice class of count `0`, and every side region that is a choice class of count `0` is
  linked (clause (B)): 0 failures.
* removed / kept / removed: 1610 hypotheses, an extra exterior region exists in all of them, and
  every one is a linked choice class of count `0`: 0 failures.
* So the Statement holds in every model instance with its hypothesis (0 failures), and it is
  not vacuous (both clauses are exercised).
* Variants that FAIL: (A) WITHOUT the pattern hypothesis (5940 extra exterior regions at most 6
  darts are not linked, in instances with no linked choice class meeting a pattern; 0 at most 5
  darts); (B) with "the first side dart" instead of "a side dart" (366 failures at most 6 darts);
  "every choice class of count `0` is linked" (165510 failures); every dart-local rule in terms of
  the pattern darts alone (already at most 5 darts, for kept / removed / kept).
* Faithfulness caveat: a Lean face class is matched with a plane region of the walk complement.
  For an extra exterior class this uses that every face class outside `K.faces` touches the walk
  (the disc is connected); this is not formalised here.

## Remaining gap

`ExtremalArcEndSurgeryStatement` only.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **A kept / removed / kept list has a `false` member.** -/
theorem extremalArcEndSurgery_false_of_krkList {α : Type*} {p : α → Bool} {l : List α}
    (h : ExtremalArcEndDescentKRKList p l) : ∃ x ∈ l, p x = false := by
  obtain ⟨_, _, B, _, _, hl, -, -, hB, hBf⟩ := h
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil B hB
  refine ⟨b, ?_, hBf b hb⟩
  rw [hl]
  simp [hb]

/-- **A removed / kept / removed list has a `false` member.** -/
theorem extremalArcEndSurgery_false_of_rkrList {α : Type*} {p : α → Bool} {l : List α}
    (h : ExtremalArcEndDescentRKRList p l) : ∃ x ∈ l, p x = false := by
  obtain ⟨_, d, _, _, _, hl, hd, -, -, -⟩ := h
  refine ⟨d, ?_, hd⟩
  rw [hl]
  simp

section Surgery

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **An extra exterior class**: the face of `z` is outside `K.faces`, and the class of `z`
avoids the exterior face and the source face. -/
def ExtremalArcEndSurgeryExtraOut (K : PocketFaceSet D eps X lo hi) (z : X.toCombMap.Dart) :
    Prop :=
  X.toCombMap.faceOf z ∉ K.faces ∧
    (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) z x) ∧
    ∀ x, X.toCombMap.faceOf x = (cell X K.source).face → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) z x

/-- **The surgery rule**: (A) every extra exterior class has linked removed runs; (B) with no
extra exterior class, some side class is a choice class of count `0`, and every such side class
has linked removed runs. -/
def ExtremalArcEndSurgeryRule (K : PocketFaceSet D eps X lo hi) : Prop :=
  (∀ z, ExtremalArcEndSurgeryExtraOut K z → ExtremalMinimalLinkedRuns K z) ∧
    ((∀ z, ¬ExtremalArcEndSurgeryExtraOut K z) →
      (∃ y ∈ K.firstSide ++ K.secondSide,
          ExtremalClassChoice K y ∧ ExtremalArcEndRemoved K y = 0) ∧
        ∀ y ∈ K.firstSide ++ K.secondSide, ExtremalClassChoice K y →
          ExtremalArcEndRemoved K y = 0 → ExtremalMinimalLinkedRuns K y)

/-- **A face class lies on one side of `K.faces`.**  A face step keeps the face; crossing an edge
off the walk keeps the side, since a dart with its face in `K.faces` and the far face outside is
a boundary dart, hence on the walk. -/
theorem extremalArcEndSurgery_mem_faces_iff (K : PocketFaceSet D eps X lo hi)
    {x y : X.toCombMap.Dart}
    (h : Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) x y) :
    X.toCombMap.faceOf x ∈ K.faces ↔ X.toCombMap.faceOf y ∈ K.faces := by
  induction h with
  | rel a _ hab =>
      rcases hab with rfl | ⟨hnk, rfl⟩
      · rw [X.toCombMap.faceOf_facePerm]
      · constructor
        · intro ha
          by_contra hb
          exact hnk (Or.inl ((K.boundary.cycle_mem_iff a).mpr ⟨ha, hb⟩))
        · intro hb
          by_contra ha
          refine hnk (Or.inr ((K.boundary.cycle_mem_iff (X.toCombMap.alpha a)).mpr ⟨hb, ?_⟩))
          rw [X.toCombMap.alpha_involutive a]
          exact ha
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **A dart outside the class, with its reverse outside, is kept.** -/
theorem extremalArcEndSurgery_kept_of_not (K : PocketFaceSet D eps X lo hi)
    (z x : X.toCombMap.Dart)
    (h₁ : ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) z x)
    (h₂ : ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) z
        (X.toCombMap.alpha x)) :
    P10ExtremalResidual.keptPred K z x = true := by
  have hc : ∀ y, ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) z y →
      regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) z y = false := by
    intro y hy
    cases hcy : regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) z y with
    | false => rfl
    | true =>
        exact absurd ((regionColour_eq_true_iff X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle) z y).mp hcy) hy
  exact (movePred_eq_true_iff X.toCombMap
    (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) z) x).mpr
    ⟨hc x h₁, hc (X.toCombMap.alpha x) h₂⟩

/-- **An extra exterior class keeps every target dart.** -/
theorem extremalArcEndSurgery_target_kept (K : PocketFaceSet D eps X lo hi)
    {z : X.toCombMap.Dart} (hz : ExtremalArcEndSurgeryExtraOut K z) {x : X.toCombMap.Dart}
    (hx : x ∈ K.targetArc.darts) : P10ExtremalResidual.keptPred K z x = true := by
  obtain ⟨hzf, hO, -⟩ := hz
  have hxc : x ∈ K.boundary.cycle := by
    rw [K.decomposition]
    exact List.mem_append.mpr (Or.inr hx)
  refine extremalArcEndSurgery_kept_of_not K z x (fun hzx => hzf ?_)
    (hO _ (P10Rose.FilterMove.faceOf_alpha_of_mem_targetArc K hx))
  exact (extremalArcEndSurgery_mem_faces_iff K hzx).mpr ((K.boundary.cycle_mem_iff x).mp hxc).1

/-- **An extra exterior class keeps every dart of the reversed source arc.** -/
theorem extremalArcEndSurgery_source_kept (K : PocketFaceSet D eps X lo hi)
    {z : X.toCombMap.Dart} (hz : ExtremalArcEndSurgeryExtraOut K z) {x : X.toCombMap.Dart}
    (hx : x ∈ invDarts X K.sourceArc.darts) : P10ExtremalResidual.keptPred K z x = true := by
  obtain ⟨hzf, -, hS⟩ := hz
  have hxc : x ∈ K.boundary.cycle := by
    rw [K.decomposition]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inr hx)))))
  have ha : X.toCombMap.alpha x ∈ K.sourceArc.darts := by
    have hx' := hx
    unfold invDarts at hx'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx'
    rw [X.toCombMap.alpha_involutive e]
    exact List.mem_reverse.mp he
  have hfa : X.toCombMap.faceOf (X.toCombMap.alpha x) = (cell X K.source).face :=
    ((X.faceBoundary (cell X K.source).face).mem_iff (X.toCombMap.alpha x)).mp
      (K.sourceArc.mem_cycle_of_mem_darts ha)
  refine extremalArcEndSurgery_kept_of_not K z x (fun hzx => hzf ?_) (hS _ hfa)
  exact (extremalArcEndSurgery_mem_faces_iff K hzx).mpr ((K.boundary.cycle_mem_iff x).mp hxc).1

/-- **An extra exterior class removes no arc dart.** -/
theorem extremalArcEndSurgery_removed_eq_zero (K : PocketFaceSet D eps X lo hi)
    {z : X.toCombMap.Dart} (hz : ExtremalArcEndSurgeryExtraOut K z) :
    ExtremalArcEndRemoved K z = 0 := by
  unfold ExtremalArcEndRemoved
  refine Nat.add_eq_zero_iff.mpr ⟨List.countP_eq_zero.mpr ?_, List.countP_eq_zero.mpr ?_⟩
  · intro x hx
    simp [extremalArcEndSurgery_target_kept K hz hx]
  · intro x hx
    simp [extremalArcEndSurgery_source_kept K hz hx]

/-- **An extra exterior class is a choice class**: it avoids the exterior and source faces by
definition, and the face of `K.kept`, which lies in `K.faces`. -/
theorem extremalArcEndSurgery_choice (K : PocketFaceSet D eps X lo hi)
    {z : X.toCombMap.Dart} (hz : ExtremalArcEndSurgeryExtraOut K z) :
    ExtremalClassChoice K z := by
  obtain ⟨hzf, hO, hS⟩ := hz
  refine ⟨Or.inr hO, Or.inr hS, K.kept, K.kept_mem, ?_⟩
  intro x hx hzx
  apply hzf
  rw [extremalArcEndSurgery_mem_faces_iff K hzx, hx]
  exact K.kept_mem

/-- **A removed arc dart makes the count positive.** -/
theorem extremalArcEndSurgery_removed_pos (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart)
    (h : (∃ x ∈ K.targetArc.darts, P10ExtremalResidual.keptPred K r x = false) ∨
      ∃ x ∈ invDarts X K.sourceArc.darts, P10ExtremalResidual.keptPred K r x = false) :
    0 < ExtremalArcEndRemoved K r := by
  apply Nat.pos_of_ne_zero
  intro h0
  unfold ExtremalArcEndRemoved at h0
  obtain ⟨hT, hS⟩ := Nat.add_eq_zero_iff.mp h0
  rcases h with ⟨x, hx, hf⟩ | ⟨x, hx, hf⟩
  · have hk := extremalArcEnd_kept_of_countP_eq_zero K r hT x hx
    rw [hf] at hk
    exact absurd hk (by decide)
  · have hk := extremalArcEnd_kept_of_countP_eq_zero K r hS x hx
    rw [hf] at hk
    exact absurd hk (by decide)

/-- **Kept / removed / kept on an arc makes the count positive.** -/
theorem extremalArcEndSurgery_removed_pos_of_krk (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart)
    (h : ExtremalArcEndDescentKRK K r K.targetArc.darts ∨
      ExtremalArcEndDescentKRK K r (invDarts X K.sourceArc.darts)) :
    0 < ExtremalArcEndRemoved K r := by
  apply extremalArcEndSurgery_removed_pos K r
  rcases h with h | h
  · exact Or.inl
      (extremalArcEndSurgery_false_of_krkList (p := P10ExtremalResidual.keptPred K r) h)
  · exact Or.inr
      (extremalArcEndSurgery_false_of_krkList (p := P10ExtremalResidual.keptPred K r) h)

/-- **Removed / kept / removed on an arc makes the count positive.** -/
theorem extremalArcEndSurgery_removed_pos_of_rkr (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart)
    (h : ExtremalArcEndDescentRKR K r K.targetArc.darts ∨
      ExtremalArcEndDescentRKR K r (invDarts X K.sourceArc.darts)) :
    0 < ExtremalArcEndRemoved K r := by
  apply extremalArcEndSurgery_removed_pos K r
  rcases h with h | h
  · exact Or.inl
      (extremalArcEndSurgery_false_of_rkrList (p := P10ExtremalResidual.keptPred K r) h)
  · exact Or.inr
      (extremalArcEndSurgery_false_of_rkrList (p := P10ExtremalResidual.keptPred K r) h)

/-- **The descent step from the rule**: at a positive count, the rule gives a linked choice class
of count `0` (an extra exterior class in case (A), a side class in case (B)). -/
theorem extremalArcEndSurgery_descent (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (hrule : ExtremalArcEndSurgeryRule K) (hpos : 0 < ExtremalArcEndRemoved K r) :
    ∃ r' : X.toCombMap.Dart, ExtremalArcEndLinked K r' ∧
      ExtremalArcEndRemoved K r' < ExtremalArcEndRemoved K r := by
  obtain ⟨hA, hB⟩ := hrule
  by_cases hex : ∃ z, ExtremalArcEndSurgeryExtraOut K z
  · obtain ⟨z, hz⟩ := hex
    refine ⟨z, ⟨extremalArcEndSurgery_choice K hz, hA z hz⟩, ?_⟩
    rw [extremalArcEndSurgery_removed_eq_zero K hz]
    exact hpos
  · obtain ⟨⟨y, hy, hyc, hy0⟩, hlink⟩ := hB (fun z hz => hex ⟨z, hz⟩)
    refine ⟨y, ⟨hyc, hlink y hy hyc hy0⟩, ?_⟩
    rw [hy0]
    exact hpos

end Surgery

/-- **OPEN (lane gl-p10-26), the one remaining planar fact.**  Under the premises of
`ExtremalArcEndDescentKRKStatement`, if a linked choice class meets the target arc or the
reversed source arc in the pattern kept / removed / kept or removed / kept / removed, the surgery
rule `ExtremalArcEndSurgeryRule K` holds.  Logically STRONGER than both pattern Statements
(`extremalArcEndSurgery_krk_of_surgery`, `extremalArcEndSurgery_rkr_of_surgery`), strictly
smaller in proof content.  0 failures in 35610 + 1610 model hypotheses up to 6 darts. -/
def ExtremalArcEndSurgeryStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∀ r : X.toCombMap.Dart, ExtremalArcEndLinked K r →
          ((ExtremalArcEndDescentKRK K r K.targetArc.darts ∨
              ExtremalArcEndDescentKRK K r (invDarts X K.sourceArc.darts)) ∨
            (ExtremalArcEndDescentRKR K r K.targetArc.darts ∨
              ExtremalArcEndDescentRKR K r (invDarts X K.sourceArc.darts))) →
          ExtremalArcEndSurgeryRule K

/-- **Endpoint, kept / removed / kept**: the surgery statement gives the pattern statement. -/
theorem extremalArcEndSurgery_krk_of_surgery
    (h : ExtremalArcEndSurgeryStatement.{u, w, v}) :
    ExtremalArcEndDescentKRKStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp
  exact extremalArcEndSurgery_descent K r
    (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr (Or.inl hp))
    (extremalArcEndSurgery_removed_pos_of_krk K r hp)

/-- **Endpoint, removed / kept / removed**: the surgery statement gives the pattern
statement. -/
theorem extremalArcEndSurgery_rkr_of_surgery
    (h : ExtremalArcEndSurgeryStatement.{u, w, v}) :
    ExtremalArcEndDescentRKRStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp
  exact extremalArcEndSurgery_descent K r
    (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr (Or.inr hp))
    (extremalArcEndSurgery_removed_pos_of_rkr K r hp)

/-- **Chain consequence**: existence and the surgery statement give the descent statement. -/
theorem extremalArcEndSurgery_descent_of_surgery
    (hE : ExtremalArcEndDescentExistsStatement.{u, w, v})
    (h : ExtremalArcEndSurgeryStatement.{u, w, v}) :
    ExtremalArcEndDescentStatement.{u, w, v} :=
  extremalArcEndDescent_of_patterns hE (extremalArcEndSurgery_krk_of_surgery h)
    (extremalArcEndSurgery_rkr_of_surgery h)

/-- **Chain consequence**: existence and the surgery statement give the Jordan arc-end
statement. -/
theorem extremalArcEndSurgery_extremalJordan_of_surgery
    (hE : ExtremalArcEndDescentExistsStatement.{u, w, v})
    (h : ExtremalArcEndSurgeryStatement.{u, w, v}) :
    ExtremalJordanStatement.{u, w, v} :=
  extremalArcEnd_extremalJordan_of_descent (extremalArcEndSurgery_descent_of_surgery hE h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndSurgery_false_of_krkList
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndSurgery_false_of_rkrList
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndSurgeryExtraOut
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndSurgeryRule
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndSurgery_mem_faces_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndSurgery_kept_of_not
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndSurgery_target_kept
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndSurgery_source_kept
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndSurgery_removed_eq_zero
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndSurgery_choice
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndSurgery_removed_pos
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndSurgery_removed_pos_of_krk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndSurgery_removed_pos_of_rkr
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndSurgery_descent
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndSurgeryStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndSurgery_krk_of_surgery
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndSurgery_rkr_of_surgery
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndSurgery_descent_of_surgery
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndSurgery_extremalJordan_of_surgery
