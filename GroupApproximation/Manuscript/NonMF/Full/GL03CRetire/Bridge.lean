import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Live.Reduction
import GroupApproximation.Manuscript.NonMF.Full.GL06f.Statement
import GroupApproximation.Meta.AxiomGuard

/-!
# GL03C retirement, part 1: the two sub-arc region move statements agree

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull` in
`non_mf_groups_exist.tex` (around line 2121); certifies no printed sentence on its own.

`Full/GL03C/Endpoint.lean` derives its four endpoints from `RoseFilterWalkStatement`, which is
FALSE (`Full.GL03C.glFix01_not_roseFilterWalk`).  The surviving open residual has two spellings.

* `GreendlingerLeaf.P10Rose.RoseRegionMoveSubArcStatement` (`P10Rose/Live/Reduction`), consumed
  by `Piece10.proof_of_regionMoveSubArc` (`P10RoseEndpoint/SingleRegion`).
* `Full.GL06f.RoseRegionMoveSubArcStatement` (`Full/GL06f/Statement`), consumed by
  `Full.GL06f.rose_of_regionMoveSubArc` in `Full/GL06/Assembly`.

## Truth check

The two statements have the same body, token for token.  Three names differ.

* `P10Rose.FilterMove.movePred` and `GL05b.movePred` both unfold to `!z d && !z (alpha d)`, so
  they are equal by `rfl` (`gl03cRetire_movePred_eq`).
* `P10Rose.FilterMove.flipFaces` and `GL06f.flipFaces` both unfold to the filter of
  `fun f => ∃ x, faceOf x = f ∧ (faceOf x ∈ faces ↔ z x = false)`.  Only the `Decidable`
  instance might differ, and it is classical in both.  They are equal by extensionality
  (`gl03cRetire_flipFaces_eq`).
* `P10ChordLift.AllNonFirstTurnsCrossed` and `GL06f.AllNonFirstTurnsCrossed` have the same body.
  The only instance in it is the classical `DecidableEq` on darts for `List.next`: the repo has no
  generic `DecidableEq` instance on `CombMap.Dart`.  So they are equivalent by `Iff.rfl`
  (`gl03cRetire_allNonFirstTurnsCrossed_iff`).

So the bridge holds in both directions (`gl03cRetire_regionMoveSubArc_iff`).  It transports the
residual only; it does not prove it.  The residual itself is OPEN and is not refuted anywhere in the
repo.
-/

namespace GroupApproximation.Full.GL03CRetire

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

/-- The two move predicates coincide (same body). -/
theorem gl03cRetire_movePred_eq (M : CombMap.{v}) (z : M.Dart → Bool) :
    GreendlingerLeaf.P10Rose.FilterMove.movePred M z = GL05b.movePred M z :=
  rfl

#audit_axioms GroupApproximation.Full.GL03CRetire.gl03cRetire_movePred_eq

/-- The two moved face sets coincide (same filter, possibly different `Decidable` instances). -/
theorem gl03cRetire_flipFaces_eq (M : CombMap.{v}) (faces : Finset M.Face)
    (z : M.Dart → Bool) :
    GreendlingerLeaf.P10Rose.FilterMove.flipFaces M faces z = GL06f.flipFaces M faces z := by
  ext f
  simp [GreendlingerLeaf.P10Rose.FilterMove.flipFaces, GL06f.flipFaces]

#audit_axioms GroupApproximation.Full.GL03CRetire.gl03cRetire_flipFaces_eq

section Vocabulary

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- The two rose configurations coincide (same body, classical `DecidableEq` on darts). -/
theorem gl03cRetire_allNonFirstTurnsCrossed_iff (K : PocketFaceSet D eps X lo hi) :
    GreendlingerLeaf.P10ChordLift.AllNonFirstTurnsCrossed K ↔
      GL06f.AllNonFirstTurnsCrossed K :=
  Iff.rfl

#audit_axioms GroupApproximation.Full.GL03CRetire.gl03cRetire_allNonFirstTurnsCrossed_iff

end Vocabulary

/-- **Bridge, forward**: the `P10Rose` sub-arc region move gives the `GL06f` one. -/
theorem gl03cRetire_gl06fRegionMoveSubArc_of_p10Rose
    (h : GreendlingerLeaf.P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    GL06f.RoseRegionMoveSubArcStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  have hmove := h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch
    ((gl03cRetire_allNonFirstTurnsCrossed_iff K).mpr hrose)
  simp only [gl03cRetire_flipFaces_eq, gl03cRetire_movePred_eq] at hmove
  exact hmove

#audit_axioms GroupApproximation.Full.GL03CRetire.gl03cRetire_gl06fRegionMoveSubArc_of_p10Rose

/-- **Bridge, backward**: the `GL06f` sub-arc region move gives the `P10Rose` one. -/
theorem gl03cRetire_p10RoseRegionMoveSubArc_of_gl06f
    (h : GL06f.RoseRegionMoveSubArcStatement.{u, w, v}) :
    GreendlingerLeaf.P10Rose.RoseRegionMoveSubArcStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  have hmove := h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch
    ((gl03cRetire_allNonFirstTurnsCrossed_iff K).mp hrose)
  simp only [← gl03cRetire_flipFaces_eq, ← gl03cRetire_movePred_eq] at hmove
  exact hmove

#audit_axioms GroupApproximation.Full.GL03CRetire.gl03cRetire_p10RoseRegionMoveSubArc_of_gl06f

/-- **The bridge**: the two spellings of the sub-arc region move are equivalent. -/
theorem gl03cRetire_regionMoveSubArc_iff :
    GreendlingerLeaf.P10Rose.RoseRegionMoveSubArcStatement.{u, w, v} ↔
      GL06f.RoseRegionMoveSubArcStatement.{u, w, v} :=
  ⟨gl03cRetire_gl06fRegionMoveSubArc_of_p10Rose, gl03cRetire_p10RoseRegionMoveSubArc_of_gl06f⟩

#audit_axioms GroupApproximation.Full.GL03CRetire.gl03cRetire_regionMoveSubArc_iff

end GroupApproximation.Full.GL03CRetire
