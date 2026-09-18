import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalClassChoice
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalMinimalLists
import GroupApproximation.Meta.AxiomGuard

/-!
# Extremal minimal: stretches from linked runs and uniform arcs

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lanes gl-p10-16, gl-p10-16c.

A sufficient condition for `ExtremalClassStretches K r`, proved here and offered as a route for
discharging the gap `ExtremalMinimalLeastStatement` of `Piece10Live/ExtremalMinimal`:

* `ExtremalMinimalLinkedRuns K r`: consecutive kept darts of `K.boundary.cycle` separated by a
  nonempty removed run have linked ends;
* `ExtremalMinimalArcUniform K r l`: all darts of `l` kept, or all removed (used for
  `K.targetArc.darts` and for the reversed source arc `invDarts X K.sourceArc.darts`).

## Proof route

A nonempty removed run `B` between a kept `d` and a kept `e` of `K.boundary.cycle` with both
ends on one arc: the arc is a middle block of `K.boundary.cycle` (`K.decomposition`, with `[]`
appended for the target arc), so `extremalMinimal_mem_segment_of_nodup` with
`K.boundary.cycle_nodup` puts a removed dart of `B` on that arc.  The arc then holds a kept dart
(`d`) and a removed one, against uniformity.

## Truth check (lane gl-p10-16)

In lane gl-p10-14's finite model: some class with the choice property, linked runs and both
arcs uniform exists in all 9010 configurations with at most 6 darts.  Uniformity is NOT a
consequence of `ExtremalClassStretches` in general (it is strictly stronger), so this module is
a sufficient condition only.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section Uniform

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A uniform arc**: all darts of `l` kept, or all removed. -/
def ExtremalMinimalArcUniform (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (l : List X.toCombMap.Dart) : Prop :=
  (∀ x ∈ l, P10ExtremalResidual.keptPred K r x = true) ∨
    ∀ x ∈ l, P10ExtremalResidual.keptPred K r x = false

/-- **Linked runs**: consecutive kept darts separated by a nonempty removed run have linked
ends. -/
def ExtremalMinimalLinkedRuns (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) :
    Prop :=
  ∀ (A : List X.toCombMap.Dart) (d : X.toCombMap.Dart) (B : List X.toCombMap.Dart)
    (e : X.toCombMap.Dart) (C : List X.toCombMap.Dart),
    K.boundary.cycle = A ++ d :: (B ++ e :: C) → P10ExtremalResidual.keptPred K r d = true →
      P10ExtremalResidual.keptPred K r e = true →
      (∀ x ∈ B, P10ExtremalResidual.keptPred K r x = false) → B ≠ [] →
        X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e

/-- **No removed run between two darts of a uniform middle block** of the boundary cycle. -/
theorem extremalMinimal_not_both_of_uniform (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart) {F S R : List X.toCombMap.Dart}
    (hdec : K.boundary.cycle = F ++ S ++ R) (hS : ExtremalMinimalArcUniform K r S)
    (A : List X.toCombMap.Dart) (d : X.toCombMap.Dart) (B : List X.toCombMap.Dart)
    (e : X.toCombMap.Dart) (C : List X.toCombMap.Dart)
    (hc : K.boundary.cycle = A ++ d :: (B ++ e :: C))
    (hd : P10ExtremalResidual.keptPred K r d = true)
    (hB : ∀ x ∈ B, P10ExtremalResidual.keptPred K r x = false) (hne : B ≠ []) :
    ¬(d ∈ S ∧ e ∈ S) := by
  intro hde
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil B hne
  have hnd : (F ++ S ++ R).Nodup := by
    rw [← hdec]
    exact K.boundary.cycle_nodup
  have hbS : b ∈ S :=
    extremalMinimal_mem_segment_of_nodup hnd (hdec.symm.trans hc) hde.1 hde.2 b hb
  rcases hS with hall | hnone
  · have hbad : true = false := (hall b hbS).symm.trans (hB b hb)
    exact absurd hbad (by decide)
  · have hbad : true = false := hd.symm.trans (hnone d hde.1)
    exact absurd hbad (by decide)

/-- **The class stretches from linked runs and uniform arcs.** -/
theorem extremalMinimal_classStretches_of_uniform (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart) (hlink : ExtremalMinimalLinkedRuns K r)
    (htgt : ExtremalMinimalArcUniform K r K.targetArc.darts)
    (hsrc : ExtremalMinimalArcUniform K r (invDarts X K.sourceArc.darts)) :
    ExtremalClassStretches K r := by
  intro A d B e C hc hd he hB hne
  have hdecT : K.boundary.cycle =
      (K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide) ++ K.targetArc.darts ++ [] :=
    K.decomposition.trans (List.append_nil _).symm
  have hdecS : K.boundary.cycle =
      K.firstSide ++ invDarts X K.sourceArc.darts ++ (K.secondSide ++ K.targetArc.darts) := by
    rw [K.decomposition]
    simp only [List.append_assoc]
  exact ⟨hlink A d B e C hc hd he hB hne,
    extremalMinimal_not_both_of_uniform K r hdecT htgt A d B e C hc hd hB hne,
    extremalMinimal_not_both_of_uniform K r hdecS hsrc A d B e C hc hd hB hne⟩

end Uniform

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalMinimalArcUniform
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalMinimalLinkedRuns
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalMinimal_not_both_of_uniform
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalMinimal_classStretches_of_uniform
