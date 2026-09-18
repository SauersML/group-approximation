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
