import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanReroute
import GroupApproximation.Meta.AxiomGuard

/-!
# The reroute statement from a pick rule on the shape pool

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-31.

**LOUD: the target `ExtremalJordanRerouteStatement` (`Piece10Live/ExtremalJordanReroute`, lane
gl-p10-30) is NOT closed outright here.**  It is reduced to ONE open Statement,
`ExtremalJordanPickStatement`, by `extremalJordanPick_extremalJordanReroute`.

## The pick rule

The *shape pool* of a pocket walk is the set of classes `r` with `ExtremalJordanPickShape K r`:
the choice property together with one removed run up to loop darts
(`ExtremalJordanRerouteLoopRun`) or a single pinning vertex (`ExtremalArcEndExistsPinned`).
The pick rule: **take a class of the shape pool with the fewest removed arc darts**
(`ExtremalArcEndRemoved`, the removed darts of the target arc and of the reversed source arc).
`ExtremalJordanPickStatement` says that the shape pool is nonempty and that every class the rule
picks meets both arcs through one end (`ExtremalArcEndBoth`).  The minimum exists by
`extremalJordanPick_exists_min`, so the rule produces the witness of the target.

Split (`extremalJordanPick_of_min`): the nonemptiness clause follows from the open statement
`ExtremalArcEndExistsPinnedStatement` of lane gl-p10-25 (a one-run class is a loop-run class,
`extremalJordanReroute_loopRun_of_oneRun`), so the new content is the pick clause alone,
`ExtremalJordanPickMinStatement`.

## LOUD: logical strength of the gap

`ExtremalJordanPickStatement` is logically STRONGER than `ExtremalJordanRerouteStatement` (it
implies it; the converse is not claimed: the target gives one good class of the pool, the pick
clause asks that every class of least count be good).  It is strictly smaller in proof content:

* the existence clause drops both arc-end conditions, and is implied by the open statement of
  lane gl-p10-25 (`ExtremalArcEndExistsPinnedStatement`), so it adds no new existence content;
* the pick clause is a local statement about one given class `r` of least count: assuming it
  fails an arc-end clause, it meets an arc as kept / removed / kept or removed / kept / removed
  (`extremalArcEndDescent_patterns_of_not_both`), and one must exhibit a class of the pool with
  fewer removed arc darts.  No simultaneous search over shape and arc ends remains; the descent
  and the choice of the minimum are proved here.

It is not an equivalent restatement (strictly stronger), and it is not one of the refuted
forms: the descent runs over the *shape* pool, not over the linked pool of lane gl-p10-21
(`ExtremalArcEndDescentStatement`, false at 8 darts), and the shape keeps the loop darts (the
loop-free variant is false, see `ExtremalJordanReroute`).

## Truth check (lane gl-p10-31, scratchpad folder `gl-p10-31/`)

TRUTHCHECK

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **A least element for a natural measure**: from one `P`-element, a `P`-element whose measure
is at most that of every `P`-element. -/
theorem extremalJordanPick_exists_min {α : Type*} (P : α → Prop) (μ : α → ℕ) (a : α)
    (ha : P a) : ∃ b, P b ∧ ∀ c, P c → μ b ≤ μ c := by
  refine extremalArcEnd_exists_of_descent P (fun b => ∀ c, P c → μ b ≤ μ c) μ ?_ a ha
  intro b _ hb
  by_contra hne
  exact hb fun c hc => Nat.not_lt.mp fun hlt => hne ⟨c, hc, hlt⟩

section PickShape

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The shape pool**: a choice class with one removed run up to loops or one pinning
vertex. -/
def ExtremalJordanPickShape (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) : Prop :=
  ExtremalClassChoice K r ∧ (ExtremalJordanRerouteLoopRun K r ∨ ExtremalArcEndExistsPinned K r)

/-- **A one-run or pinned choice class lies in the shape pool.** -/
theorem extremalJordanPick_shape_of_oneRun (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart) (hc : ExtremalClassChoice K r)
    (h : ExtremalArcEndExistsOneRun K r ∨ ExtremalArcEndExistsPinned K r) :
    ExtremalJordanPickShape K r := by
  rcases h with h | h
  · exact ⟨hc, Or.inl (extremalJordanReroute_loopRun_of_oneRun K r h)⟩
  · exact ⟨hc, Or.inr h⟩

end PickShape

/-- **OPEN (lane gl-p10-31).**  Under the premises of `ExtremalJordanStatement`: the shape pool
is nonempty, and every class of the shape pool with the fewest removed arc darts meets both arcs
through one end.  LOUD: logically STRONGER than `ExtremalJordanRerouteStatement`
(`extremalJordanPick_extremalJordanReroute`), strictly smaller in proof content (the arc-end
conditions are decoupled from the existence of a shaped class, the minimum is taken here); true
in the model (see the module docstring). -/
def ExtremalJordanPickStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        (∃ r : X.toCombMap.Dart, ExtremalJordanPickShape K r) ∧
        ∀ r : X.toCombMap.Dart, ExtremalJordanPickShape K r →
          (∀ r' : X.toCombMap.Dart, ExtremalJordanPickShape K r' →
            ExtremalArcEndRemoved K r ≤ ExtremalArcEndRemoved K r') →
          ExtremalArcEndBoth K r

/-- **OPEN (lane gl-p10-31), the pick clause alone.**  Under the premises of
`ExtremalJordanStatement`, every class of the shape pool with the fewest removed arc darts meets
both arcs through one end.  Logically WEAKER than `ExtremalJordanPickStatement`; true in the
model (see the module docstring). -/
def ExtremalJordanPickMinStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∀ r : X.toCombMap.Dart, ExtremalJordanPickShape K r →
          (∀ r' : X.toCombMap.Dart, ExtremalJordanPickShape K r' →
            ExtremalArcEndRemoved K r ≤ ExtremalArcEndRemoved K r') →
          ExtremalArcEndBoth K r

/-- **The reroute statement from the pick rule**: take a class of least count in the shape
pool. -/
theorem extremalJordanPick_extremalJordanReroute (h : ExtremalJordanPickStatement.{u, w, v}) :
    ExtremalJordanRerouteStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨⟨r₀, h₀⟩, hmin⟩ :=
    h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hr, hle⟩ := extremalJordanPick_exists_min (ExtremalJordanPickShape K)
    (ExtremalArcEndRemoved K) r₀ h₀
  obtain ⟨hT, hS⟩ := hmin r hr hle
  obtain ⟨hc, hp⟩ := hr
  exact ⟨r, hc, hp, hT, hS⟩

/-- **The split**: the pick statement from the one-run-or-pinned existence statement of lane
gl-p10-25 and the pick clause. -/
theorem extremalJordanPick_of_min (hE : ExtremalArcEndExistsPinnedStatement.{u, w, v})
    (hM : ExtremalJordanPickMinStatement.{u, w, v}) :
    ExtremalJordanPickStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hc, hp⟩ := hE D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨⟨r, extremalJordanPick_shape_of_oneRun K r hc hp⟩,
    hM D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose⟩

/-- **The pick statement gives the pick clause.** -/
theorem extremalJordanPick_min_of_pick (h : ExtremalJordanPickStatement.{u, w, v}) :
    ExtremalJordanPickMinStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose).2

/-- **Chain consequence**: the Jordan arc-end statement from the pick statement. -/
theorem extremalJordanPick_extremalJordan (h : ExtremalJordanPickStatement.{u, w, v}) :
    ExtremalJordanStatement.{u, w, v} :=
  extremalJordanReroute_extremalJordan (extremalJordanPick_extremalJordanReroute h)

/-- **Chain consequence**: the relative Greendlinger statement from the four-piece-off
statement and the pick statement. -/
theorem extremalJordanPick_relativeGreendlinger
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : ExtremalJordanPickStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  extremalJordanReroute_relativeGreendlinger hoff (extremalJordanPick_extremalJordanReroute h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPick_exists_min
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickShape
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPick_shape_of_oneRun
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickMinStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPick_extremalJordanReroute
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPick_of_min
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPick_min_of_pick
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPick_extremalJordan
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPick_relativeGreendlinger

