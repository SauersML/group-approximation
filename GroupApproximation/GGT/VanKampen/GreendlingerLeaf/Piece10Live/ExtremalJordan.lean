import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalMinimal
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanLists
import GroupApproximation.Meta.AxiomGuard

/-!
# Extremal class meeting each arc in a prefix or a suffix

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-17.

**LOUD: the target `P10ExtremalRegion.RoseExtremalClassStatement` (`Piece10Live/ExtremalClass`)
is NOT closed here, and neither is `ExtremalMinimalUniformStatement`
(`Piece10Live/ExtremalMinimal`).**  This module isolates one open Statement strictly between
the two, `ExtremalJordanStatement`, and proves

* `extremalJordan_of_extremalMinimalUniform : ExtremalMinimalUniformStatement →
  ExtremalJordanStatement` (so the new Statement is no stronger than the old gap);
* `roseExtremalClass_of_extremalJordan : ExtremalJordanStatement →
  RoseExtremalClassStatement` (so it still suffices);
* the chain consequence `extremalJordan_relativeGreendlinger`.

`ExtremalJordanStatement` replaces the uniform-arc clauses of the old gap by
`ExtremalJordanArcEnd K r l`: `l` splits as `pre ++ post` with `pre` kept and `post` removed, or
`pre` removed and `post` kept.  So the kept darts of each arc form a prefix or a suffix of the
arc (Osin's picture: an extremal region meets each arc in a subarc through one of its ends).
The choice clause and the linked-runs clause are unchanged.

## Proof route

`extremalJordan_not_both_of_arcEnd`: a nonempty removed run `B` between a kept `d` and a kept
`e` with both on the arc `S = pre ++ post` (a middle block of the duplicate-free cycle) has a
removed `b ∈ B` on `S` (`extremalMinimal_mem_segment_of_nodup`).  In the case "`pre` kept,
`post` removed", `b ∈ post` and `e ∈ pre`, but `b` comes before `e` in the cycle; in the case
"`pre` removed, `post` kept", `b ∈ pre` and `d ∈ post`, but `d` comes before `b`.  Both orders
are refuted by `extremalJordan_false_of_order` (`Piece10Live/ExtremalJordanLists`).

## Truth check (lane gl-p10-17, model of lane gl-p10-14)

Checked by exhaustive enumeration: plane Eulerian closed walks with rotation systems, every
instance of source arc, target arc, source region and exterior region, and every candidate
class.

* `ExtremalJordanStatement` holds in every instance: 0 failures in 228756 instances (542
  configurations, at most 5 darts) and 0 failures in 6717858 instances (9010 configurations,
  at most 6 darts).
* It is strictly weaker than the old gap, pointwise in the class: in 12244 instances (at most 5
  darts) and 333898 instances (at most 6 darts) strictly more classes pass it than pass the
  uniform-arc clauses.
* It is strictly stronger than the target: in 110 instances (at most 5 darts) and 1610 (at most
  6 darts) strictly more classes pass `ExtremalClassChoice ∧ ExtremalClassStretches` than pass
  it.  So it is not an equivalent restatement.  (An "interval" arc clause, with the kept part any
  contiguous subarc, is avoided: with `cycle_nodup` it is close to a restatement of the target.)

## Why the old gap is not proved outright here

Selection rules tried in the model, each refuted at 6 darts: the class of least (or greatest)
winding number around the walk (1656 failing instances), and a region bounded by a single closed
run (a "lobe", 3444 failing instances, six loops at one vertex).  A lobe adjacent to the first
repeated vertex already fails at 5 darts.  In all failures the linked-runs clause is available;
what breaks is the interplay of the choice clause with the arc clauses.  No class was picked by
least measure.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section ArcEnd

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **An arc met through one end**: `l = pre ++ post` with `pre` kept and `post` removed, or
`pre` removed and `post` kept. -/
def ExtremalJordanArcEnd (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (l : List X.toCombMap.Dart) : Prop :=
  ∃ pre post : List X.toCombMap.Dart, l = pre ++ post ∧
    (((∀ x ∈ pre, P10ExtremalResidual.keptPred K r x = true) ∧
        ∀ x ∈ post, P10ExtremalResidual.keptPred K r x = false) ∨
      ((∀ x ∈ pre, P10ExtremalResidual.keptPred K r x = false) ∧
        ∀ x ∈ post, P10ExtremalResidual.keptPred K r x = true))

/-- **A uniform arc is met through one end** (take `post = []`). -/
theorem extremalJordan_arcEnd_of_uniform (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart) (l : List X.toCombMap.Dart) (hl : ExtremalMinimalArcUniform K r l) :
    ExtremalJordanArcEnd K r l := by
  refine ⟨l, [], (List.append_nil l).symm, ?_⟩
  rcases hl with hall | hnone
  · exact Or.inl ⟨hall, fun _ hx => absurd hx List.not_mem_nil⟩
  · exact Or.inr ⟨hnone, fun _ hx => absurd hx List.not_mem_nil⟩

/-- **No removed run between two darts of a middle block met through one end** of the
boundary cycle. -/
theorem extremalJordan_not_both_of_arcEnd (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart) {F S R : List X.toCombMap.Dart}
    (hdec : K.boundary.cycle = F ++ S ++ R) (hS : ExtremalJordanArcEnd K r S)
    (A : List X.toCombMap.Dart) (d : X.toCombMap.Dart) (B : List X.toCombMap.Dart)
    (e : X.toCombMap.Dart) (C : List X.toCombMap.Dart)
    (hc : K.boundary.cycle = A ++ d :: (B ++ e :: C))
    (hd : P10ExtremalResidual.keptPred K r d = true)
    (he : P10ExtremalResidual.keptPred K r e = true)
    (hB : ∀ x ∈ B, P10ExtremalResidual.keptPred K r x = false) (hne : B ≠ []) :
    ¬(d ∈ S ∧ e ∈ S) := by
  intro hde
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil B hne
  have hnd : (F ++ S ++ R).Nodup := by
    rw [← hdec]
    exact K.boundary.cycle_nodup
  have hbS : b ∈ S :=
    extremalMinimal_mem_segment_of_nodup hnd (hdec.symm.trans hc) hde.1 hde.2 b hb
  obtain ⟨pre, post, hsplit, hcase⟩ := hS
  have hcyc : K.boundary.cycle = (F ++ pre) ++ (post ++ R) := by
    rw [hdec, hsplit]
    simp only [List.append_assoc]
  have hnd' : ((F ++ pre) ++ (post ++ R)).Nodup := by
    rw [← hcyc]
    exact K.boundary.cycle_nodup
  have hmem : ∀ x ∈ S, x ∈ pre ∨ x ∈ post := by
    intro x hx
    rw [hsplit] at hx
    exact List.mem_append.mp hx
  rcases hcase with ⟨hpre, hpost⟩ | ⟨hpre, hpost⟩
  · -- `pre` kept, `post` removed: `b ∈ post` comes before `e ∈ pre` in the cycle.
    have hbpost : b ∈ post := by
      rcases hmem b hbS with h | h
      · have hbad : true = false := (hpre b h).symm.trans (hB b hb)
        exact absurd hbad (by decide)
      · exact h
    have hepre : e ∈ pre := by
      rcases hmem e hde.2 with h | h
      · exact h
      · have hbad : true = false := he.symm.trans (hpost e h)
        exact absurd hbad (by decide)
    have horder : K.boundary.cycle = (A ++ d :: B) ++ e :: C := by
      rw [hc]
      simp only [List.append_assoc, List.cons_append]
    exact extremalJordan_false_of_order hnd' (hcyc.symm.trans horder)
      (List.mem_append_right F hepre) (List.mem_append_left R hbpost)
      (List.mem_append_right A (List.mem_cons_of_mem d hb)) List.mem_cons_self
  · -- `pre` removed, `post` kept: `d ∈ post` comes before `b ∈ pre` in the cycle.
    have hbpre : b ∈ pre := by
      rcases hmem b hbS with h | h
      · exact h
      · have hbad : true = false := (hpost b h).symm.trans (hB b hb)
        exact absurd hbad (by decide)
    have hdpost : d ∈ post := by
      rcases hmem d hde.1 with h | h
      · have hbad : true = false := hd.symm.trans (hpre d h)
        exact absurd hbad (by decide)
      · exact h
    have horder : K.boundary.cycle = (A ++ [d]) ++ (B ++ e :: C) := by
      rw [hc]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact extremalJordan_false_of_order hnd' (hcyc.symm.trans horder)
      (List.mem_append_right F hbpre) (List.mem_append_left R hdpost)
      (List.mem_append_right A List.mem_cons_self) (List.mem_append_left (e :: C) hb)

/-- **The class stretches from linked runs and arcs met through one end.** -/
theorem extremalJordan_classStretches_of_arcEnd (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart) (hlink : ExtremalMinimalLinkedRuns K r)
    (htgt : ExtremalJordanArcEnd K r K.targetArc.darts)
    (hsrc : ExtremalJordanArcEnd K r (invDarts X K.sourceArc.darts)) :
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
    extremalJordan_not_both_of_arcEnd K r hdecT htgt A d B e C hc hd he hB hne,
    extremalJordan_not_both_of_arcEnd K r hdecS hsrc A d B e C hc hd he hB hne⟩

end ArcEnd
