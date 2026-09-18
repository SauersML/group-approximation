import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalArcEndDescent
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalArcEndExistsParity
import GroupApproximation.Meta.AxiomGuard

/-!
# Linked removed runs from a single run or a single pinning vertex

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-25.

**LOUD: the target `P10ExtremalRegion.ExtremalArcEndDescentExistsStatement`
(`Piece10Live/ExtremalArcEndDescent`, lane gl-p10-22) is NOT closed outright here.**  It is
reduced to ONE open Statement, `ExtremalArcEndExistsPinnedStatement`, by
`extremalArcEndExists_exists_of_pinned`.

The linked-runs half of `ExtremalArcEndLinked` is proved from either of two local shapes of the
removed darts of a choice class `r` on the pocket walk:

* `ExtremalArcEndExistsOneRun K r`: the walk splits as `A ++ B ++ C` with `A`, `C` of one kind
  and `B` of the other (cyclically at most one removed run).  Proof
  (`extremalArcEndExists_linked_of_oneRun`): a nonempty gap between two kept darts is then all of
  the removed run and every other dart is kept, so the parity count at a vertex
  (`extremalArcEndExists_closed_run`, `Piece10Live/ExtremalArcEndExistsParity`) links its ends.
* `ExtremalArcEndExistsPinned K r`: every kept / removed change of consecutive walk darts lands
  at one vertex `w`.  Proof (`extremalArcEndExists_linked_of_pinned`): both ends of a gap are
  at `w`, glued by the walk chain.

Proved (no gap): `extremalArcEndExists_closed_run_pocket`, `extremalArcEndExists_linked_of_pinned`,
`extremalArcEndExists_linked_of_oneRun`, `extremalArcEndExists_exists_of_pinned`, and the chain
consequences `extremalArcEndExists_descent_of_pinned`,
`extremalArcEndExists_extremalJordan_of_pinned`, `extremalArcEndExists_relativeGreendlinger`.

## LOUD: logical strength of the gap

`ExtremalArcEndExistsPinnedStatement` is logically STRONGER than the target
`ExtremalArcEndDescentExistsStatement` (it implies it, `extremalArcEndExists_exists_of_pinned`;
the converse is not claimed): it asks for a choice class whose removed darts have one of two
explicit local shapes, not merely linked runs.  It is smaller in proof content: the parity
argument that turns a lone removed run into a linked one is done here, so what remains is the
existence of a choice class with a lone run or a single pinning vertex.  It is not proved
outright: producing such a class is planar region theory with no corpus support.

## Truth check (lane gl-p10-25)

Scripts `single.py`, `pinned.py`, `fail6.py` in the scratchpad folder `gl-p10-25/`, on the
enumerations of lane gl-p10-21 (every instance of pocket walk, arcs, source and exterior
regions, every candidate choice class):

* at most 5 darts, 228756 instances: a choice class with one cyclic removed run exists in all
  228756; a pinned choice class exists in all 228756;
* at most 6 darts, 6717858 instances: a pinned choice class exists in all 6717858, and every
  pinned class has linked runs (0 exceptions); a one-run class exists in only 6714558.
* **OneRun alone is FALSE at 6 darts** (3300 instances, bouquet walks with two removed runs,
  both linked, e.g. `RkkRkk`), which is why the Statement asks for OneRun OR Pinned.

The model checks the cyclic forms, which imply the linear forms stated here.

## Remaining gap

`ExtremalArcEndExistsPinnedStatement`: open, STRONGER than the target, true in the model up to
6 darts.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section ExistsRuns

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **One removed run**: the pocket walk splits as `A ++ B ++ C` with the darts of `A` and `C`
of one kind (kept or removed) and the darts of `B` of the other. -/
def ExtremalArcEndExistsOneRun (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) :
    Prop :=
  ∃ A B C : List X.toCombMap.Dart, K.boundary.cycle = A ++ B ++ C ∧
    (((∀ x ∈ A, P10ExtremalResidual.keptPred K r x = true) ∧
        (∀ x ∈ B, P10ExtremalResidual.keptPred K r x = false) ∧
        (∀ x ∈ C, P10ExtremalResidual.keptPred K r x = true)) ∨
      ((∀ x ∈ A, P10ExtremalResidual.keptPred K r x = false) ∧
        (∀ x ∈ B, P10ExtremalResidual.keptPred K r x = true) ∧
        (∀ x ∈ C, P10ExtremalResidual.keptPred K r x = false)))

/-- **One pinning vertex**: every change between kept and removed along consecutive darts of
the pocket walk happens at the vertex `w`. -/
def ExtremalArcEndExistsPinned (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) :
    Prop :=
  ∃ w : X.toCombMap.Vertex, ∀ (A C : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
    K.boundary.cycle = A ++ x :: y :: C →
      P10ExtremalResidual.keptPred K r x ≠ P10ExtremalResidual.keptPred K r y →
        X.toCombMap.vertexOf y = w

/-- **A lone removed run on the pocket walk is linked**: the parity count at a vertex. -/
theorem extremalArcEndExists_closed_run_pocket (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) (r : X.toCombMap.Dart) {A B C : List X.toCombMap.Dart}
    {d e : X.toCombMap.Dart} (hdec : K.boundary.cycle = A ++ d :: (B ++ e :: C))
    (hA : ∀ x ∈ A, P10ExtremalResidual.keptPred K r x = true)
    (hd : P10ExtremalResidual.keptPred K r d = true)
    (hB : ∀ x ∈ B, P10ExtremalResidual.keptPred K r x = false)
    (he : P10ExtremalResidual.keptPred K r e = true)
    (hC : ∀ x ∈ C, P10ExtremalResidual.keptPred K r x = true) :
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e :=
  extremalArcEndExists_closed_run X.toCombMap K.boundary.cycle_mem_iff K.boundary.cycle_nodup
    hK.1 (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r)
    (regionColour_step X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r)
    (regionColour_indep K.boundary.cycle_mem_iff r) hdec hA hd hB he hC

/-- **A pinned class has linked runs**: both ends of a removed gap are at the pinning vertex. -/
theorem extremalArcEndExists_linked_of_pinned (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) (r : X.toCombMap.Dart) (h : ExtremalArcEndExistsPinned K r) :
    ExtremalMinimalLinkedRuns K r := by
  obtain ⟨w, hw⟩ := h
  intro A d B e C hdec hd he hB hne
  obtain ⟨b, L, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hdec1 : K.boundary.cycle = A ++ d :: b :: (L ++ e :: C) := by
    rw [hdec, List.cons_append]
  have hvb : X.toCombMap.vertexOf b = w :=
    hw A (L ++ e :: C) d b hdec1 (by
      rw [hd, hB b (by simp)]
      decide)
  have hdb : X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf b := by
    have hc := hK.1
    rw [hdec1] at hc
    exact (List.isChain_append_cons_cons.mp hc).2.1
  obtain ⟨L0, l, hl⟩ : ∃ L0 l, b :: L = L0 ++ [l] :=
    ⟨_, _, (List.dropLast_append_getLast (List.cons_ne_nil b L)).symm⟩
  have hdec2 : K.boundary.cycle = (A ++ d :: L0) ++ l :: e :: C := by
    rw [hdec, hl]
    simp
  have hlmem : l ∈ b :: L := by
    rw [hl]
    simp
  have hve : X.toCombMap.vertexOf e = w :=
    hw _ C l e hdec2 (by
      rw [hB l hlmem, he]
      decide)
  exact hdb.trans (hvb.trans hve.symm)

/-- **A class with one removed run has linked runs.** -/
theorem extremalArcEndExists_linked_of_oneRun (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) (r : X.toCombMap.Dart) (h : ExtremalArcEndExistsOneRun K r) :
    ExtremalMinimalLinkedRuns K r := by
  obtain ⟨A, B, C, hdec, ⟨hA, hB, hC⟩ | ⟨hA, hB, hC⟩⟩ := h
  · have hnd : (A ++ B ++ C).Nodup := by
      rw [← hdec]
      exact K.boundary.cycle_nodup
    have hrem : ∀ x ∈ A ++ B ++ C, P10ExtremalResidual.keptPred K r x = false → x ∈ B := by
      intro x hx hxk
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact absurd ((hA x hx).symm.trans hxk) (by decide)
        · exact hx
      · exact absurd ((hC x hx).symm.trans hxk) (by decide)
    intro A0 d B0 e C0 hdec0 hd he hB0 hne
    obtain ⟨b, L, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hbB : b ∈ B := hrem b (by
      rw [← hdec, hdec0]
      simp) (hB0 b (by simp))
    refine extremalArcEndExists_closed_run_pocket K hK r hdec0 ?_ hd hB0 he ?_
    · intro x hx
      cases hxk : P10ExtremalResidual.keptPred K r x with
      | true => rfl
      | false =>
        exfalso
        obtain ⟨A1, A2, rfl⟩ := List.append_of_mem hx
        have hxB : x ∈ B := hrem x (by
          rw [← hdec, hdec0]
          simp) hxk
        have hseg := extremalMinimal_mem_segment_of_nodup hnd
          (show A ++ B ++ C = A1 ++ x :: ((A2 ++ [d]) ++ b :: (L ++ e :: C0)) by
            rw [← hdec, hdec0]
            simp) hxB hbB
        exact absurd (hd.symm.trans (hB d (hseg d (by simp)))) (by decide)
    · intro x hx
      cases hxk : P10ExtremalResidual.keptPred K r x with
      | true => rfl
      | false =>
        exfalso
        obtain ⟨C1, C2, rfl⟩ := List.append_of_mem hx
        have hxB : x ∈ B := hrem x (by
          rw [← hdec, hdec0]
          simp) hxk
        have hseg := extremalMinimal_mem_segment_of_nodup hnd
          (show A ++ B ++ C = (A0 ++ [d]) ++ b :: ((L ++ e :: C1) ++ x :: C2) by
            rw [← hdec, hdec0]
            simp) hbB hxB
        exact absurd (he.symm.trans (hB e (hseg e (by simp)))) (by decide)
  · have hnd : (A ++ B ++ C).Nodup := by
      rw [← hdec]
      exact K.boundary.cycle_nodup
    have hkeptB : ∀ x ∈ A ++ B ++ C, P10ExtremalResidual.keptPred K r x = true → x ∈ B := by
      intro x hx hxk
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact absurd ((hA x hx).symm.trans hxk) (by decide)
        · exact hx
      · exact absurd ((hC x hx).symm.trans hxk) (by decide)
    intro A0 d B0 e C0 hdec0 hd he hB0 hne
    obtain ⟨b, L, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hdB : d ∈ B := hkeptB d (by
      rw [← hdec, hdec0]
      simp) hd
    have heB : e ∈ B := hkeptB e (by
      rw [← hdec, hdec0]
      simp) he
    have hseg := extremalMinimal_mem_segment_of_nodup hnd (hdec.symm.trans hdec0) hdB heB
    exact absurd ((hB b (hseg b (by simp))).symm.trans (hB0 b (by simp))) (by decide)

end ExistsRuns

/-- **OPEN (lane gl-p10-25).**  Under the premises of `ExtremalJordanStatement`, a choice class
exists whose removed darts form one run or change kind only at one vertex.  Logically STRONGER
than `ExtremalArcEndDescentExistsStatement`; true in the model up to 6 darts (the one-run
alternative alone fails at 6 darts). -/
def ExtremalArcEndExistsPinnedStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ r : X.toCombMap.Dart, ExtremalClassChoice K r ∧
          (ExtremalArcEndExistsOneRun K r ∨ ExtremalArcEndExistsPinned K r)

/-- **The existence statement from a one-run or pinned choice class.** -/
theorem extremalArcEndExists_exists_of_pinned
    (h : ExtremalArcEndExistsPinnedStatement.{u, w, v}) :
    ExtremalArcEndDescentExistsStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hc, hp⟩ := h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  rcases hp with hp | hp
  · exact ⟨r, ⟨hc, extremalArcEndExists_linked_of_oneRun K hK r hp⟩⟩
  · exact ⟨r, ⟨hc, extremalArcEndExists_linked_of_pinned K hK r hp⟩⟩

/-- **Chain consequence**: the arc-end descent statement. -/
theorem extremalArcEndExists_descent_of_pinned
    (h : ExtremalArcEndExistsPinnedStatement.{u, w, v})
    (hKRK : ExtremalArcEndDescentKRKStatement.{u, w, v})
    (hRKR : ExtremalArcEndDescentRKRStatement.{u, w, v}) :
    ExtremalArcEndDescentStatement.{u, w, v} :=
  extremalArcEndDescent_of_patterns (extremalArcEndExists_exists_of_pinned h) hKRK hRKR

/-- **Chain consequence**: the Jordan arc-end statement. -/
theorem extremalArcEndExists_extremalJordan_of_pinned
    (h : ExtremalArcEndExistsPinnedStatement.{u, w, v})
    (hKRK : ExtremalArcEndDescentKRKStatement.{u, w, v})
    (hRKR : ExtremalArcEndDescentRKRStatement.{u, w, v}) :
    ExtremalJordanStatement.{u, w, v} :=
  extremalArcEndDescent_extremalJordan_of_patterns (extremalArcEndExists_exists_of_pinned h)
    hKRK hRKR

/-- **Chain consequence**: the relative Greendlinger statement from the four-piece-off
statement, the pinned existence statement and the two pattern statements. -/
theorem extremalArcEndExists_relativeGreendlinger
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : ExtremalArcEndExistsPinnedStatement.{u, w, v})
    (hKRK : ExtremalArcEndDescentKRKStatement.{u, w, v})
    (hRKR : ExtremalArcEndDescentRKRStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  extremalArcEndDescent_relativeGreendlinger hoff (extremalArcEndExists_exists_of_pinned h)
    hKRK hRKR

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndExistsOneRun
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndExistsPinned
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_closed_run_pocket
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_linked_of_pinned
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_linked_of_oneRun
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndExistsPinnedStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_exists_of_pinned
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_descent_of_pinned
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_extremalJordan_of_pinned
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_relativeGreendlinger
