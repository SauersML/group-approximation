import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordan
import GroupApproximation.Meta.AxiomGuard

/-!
# The extremal class of fewest removed arc darts

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-21.

**LOUD: the target `P10ExtremalRegion.ExtremalJordanStatement` (`Piece10Live/ExtremalJordan`)
is NOT closed here.**  This module records the class-choice rule found in the finite model and
reduces the target to it by a well-founded descent, proved fully:

* `extremalArcEnd_exists_of_descent`: a generic descent lemma over a `ℕ`-valued measure;
* `extremalArcEnd_both_of_removed_eq_zero`: a class removing no arc dart meets both arcs through
  one end (so the descent clause below is only ever used at a positive count);
* `extremalArcEnd_extremalJordan_of_descent : ExtremalArcEndDescentStatement →
  ExtremalJordanStatement`, and the chain consequence `extremalArcEnd_relativeGreendlinger`.

## The rule

Among the classes `r` with `ExtremalClassChoice K r ∧ ExtremalMinimalLinkedRuns K r` (a
*linked choice class*, `ExtremalArcEndLinked`), take one with the fewest removed arc darts
(`ExtremalArcEndRemoved K r`: darts of `K.targetArc.darts` plus darts of
`invDarts X K.sourceArc.darts` with `keptPred K r = false`).  Such a class meets both arcs through
one end (`ExtremalArcEndBoth`, i.e. both `ExtremalJordanArcEnd` clauses).

The open `ExtremalArcEndDescentStatement` states the rule in descent form: a linked choice class
exists, and a linked choice class failing one of the two arc-end clauses can be replaced by a
linked choice class with strictly fewer removed arc darts.  (Classically this is the same as
"every least linked choice class meets both arcs through one end".)

## Proof route of the reduction

Strong induction on the count (`Nat.strong_induction_on`): start from the linked choice class of
the existence clause; if it fails an arc-end clause, the descent clause gives a linked choice
class of smaller count.  The class reached satisfies `ExtremalClassChoice`, linked runs and both
arc-end clauses, which is `ExtremalJordanStatement`.

## Truth check (lane gl-p10-21, model of lanes gl-p10-14 / gl-p10-17)

Pocket boundary as a plane Eulerian closed walk with a rotation system, regions coloured
inside/outside `K.faces`, every non-first turn crossed, every instance of source arc, target arc,
source region and exterior region, and every candidate class (scripts in the scratchpad folder
`gl-p10-21/`, `check_rule.py`, `linkrule.py`).

* A linked choice class exists in every instance (228756 instances at most 5 darts, 6717858 at
  most 6 darts).
* Every linked choice class of fewest removed arc darts satisfies both arc-end clauses: 0
  failures in all those instances.  So the descent clause holds in the model.  Partial run at
  exactly 7 darts: the first 40000 configurations (52677912 instances), 0 failures of either.
* The descent clause is not vacuous: at most 5 darts, 980 linked choice classes fail an arc-end
  clause (patterns kept/removed/kept and removed/kept/removed on one arc).
* Rules that FAIL: most removed arc darts (790 instances at 5 darts), most or fewest removed
  darts overall (540 at 5 darts), and "a linked choice class touching no arc dart" (24 instances
  at 6 darts, all with one-dart source and target arcs, where every good class touches an arc).

## LOUD: logical strength

`ExtremalArcEndDescentStatement` is logically STRONGER than `ExtremalJordanStatement`: its
existence clause is implied by it, but the descent clause quantifies over all linked choice
classes and is not implied by the existence of one good class.  It is strictly smaller in proof
content: the choice of the class (the well-founded minimisation over the count) is proved here,
and what remains is a local surgery statement at one linked choice class with an arc met
through neither end, together with the existence of one linked choice class.  (A logically weaker
Statement with a proved `_of_` reduction to the target would be equivalent to it.)

## Remaining gap

`ExtremalArcEndDescentStatement`: (i) a linked choice class exists; (ii) at a linked choice class
meeting an arc in the pattern kept/removed/kept or removed/kept/removed, a planar surgery giving a
linked choice class with fewer removed arc darts.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **Descent**: if every `P`-element failing `Q` has a `P`-element of smaller measure, then from
one `P`-element we reach a `P`-element satisfying `Q`. -/
theorem extremalArcEnd_exists_of_descent {α : Type*} (P Q : α → Prop) (μ : α → ℕ)
    (hdesc : ∀ a, P a → ¬Q a → ∃ b, P b ∧ μ b < μ a) (a : α) (ha : P a) :
    ∃ b, P b ∧ Q b := by
  have key : ∀ n : ℕ, ∀ x : α, μ x = n → P x → ∃ b, P b ∧ Q b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hμ hx
      by_cases hq : Q x
      · exact ⟨x, hx, hq⟩
      · obtain ⟨b, hb, hlt⟩ := hdesc x hx hq
        exact ih (μ b) (lt_of_lt_of_eq hlt hμ) b rfl hb
  exact key (μ a) a rfl ha

section ArcEndLeast

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Removed arc darts**: the darts of the target arc and of the reversed source arc that the
class `r` removes (`keptPred K r = false`). -/
noncomputable def ExtremalArcEndRemoved (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart) : ℕ :=
  K.targetArc.darts.countP (fun x => !P10ExtremalResidual.keptPred K r x) +
    (invDarts X K.sourceArc.darts).countP (fun x => !P10ExtremalResidual.keptPred K r x)

/-- **A linked choice class**: the choice property and linked removed runs. -/
def ExtremalArcEndLinked (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) : Prop :=
  ExtremalClassChoice K r ∧ ExtremalMinimalLinkedRuns K r

/-- **Both arcs met through one end**: the two arc-end clauses of `ExtremalJordanStatement`. -/
def ExtremalArcEndBoth (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) : Prop :=
  ExtremalJordanArcEnd K r K.targetArc.darts ∧
    ExtremalJordanArcEnd K r (invDarts X K.sourceArc.darts)

/-- **No removed dart counted**: every dart of the list is kept. -/
theorem extremalArcEnd_kept_of_countP_eq_zero (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart) {l : List X.toCombMap.Dart}
    (hl : l.countP (fun x => !P10ExtremalResidual.keptPred K r x) = 0) :
    ∀ x ∈ l, P10ExtremalResidual.keptPred K r x = true := by
  intro x hx
  have h : ¬((!P10ExtremalResidual.keptPred K r x) = true) :=
    (List.countP_eq_zero.mp hl) x hx
  revert h
  cases P10ExtremalResidual.keptPred K r x <;> decide

/-- **A class removing no arc dart meets both arcs through one end.** -/
theorem extremalArcEnd_both_of_removed_eq_zero (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart) (h0 : ExtremalArcEndRemoved K r = 0) :
    ExtremalArcEndBoth K r := by
  unfold ExtremalArcEndRemoved at h0
  obtain ⟨hT, hS⟩ := Nat.add_eq_zero_iff.mp h0
  exact ⟨extremalJordan_arcEnd_of_uniform K r _
      (Or.inl (extremalArcEnd_kept_of_countP_eq_zero K r hT)),
    extremalJordan_arcEnd_of_uniform K r _
      (Or.inl (extremalArcEnd_kept_of_countP_eq_zero K r hS))⟩

end ArcEndLeast

/-- **OPEN (lane gl-p10-21).**  Under the premises of `ExtremalJordanStatement`: a linked choice
class exists, and a linked choice class meeting one of the two arcs through neither end can be
replaced by a linked choice class with strictly fewer removed arc darts.  Model-checked (0
failures up to 6 darts, see the module docstring).  Logically STRONGER than
`ExtremalJordanStatement`, strictly smaller in proof content. -/
def ExtremalArcEndDescentStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        (∃ r : X.toCombMap.Dart, ExtremalArcEndLinked K r) ∧
        ∀ r : X.toCombMap.Dart, ExtremalArcEndLinked K r → ¬ExtremalArcEndBoth K r →
          ∃ r' : X.toCombMap.Dart, ExtremalArcEndLinked K r' ∧
            ExtremalArcEndRemoved K r' < ExtremalArcEndRemoved K r

/-- **The descent statement implies the Jordan arc-end statement**: descend along the count of
removed arc darts from the linked choice class of the existence clause. -/
theorem extremalArcEnd_extremalJordan_of_descent
    (h : ExtremalArcEndDescentStatement.{u, w, v}) :
    ExtremalJordanStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨⟨r₀, h₀⟩, hdesc⟩ :=
    h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, ⟨hc, hl⟩, hT, hS⟩ :=
    extremalArcEnd_exists_of_descent (ExtremalArcEndLinked K) (ExtremalArcEndBoth K)
      (ExtremalArcEndRemoved K) hdesc r₀ h₀
  exact ⟨r, hc, hl, hT, hS⟩

/-- **Chain consequence**: the relative Greendlinger statement from the four-piece-off
statement and the descent statement. -/
theorem extremalArcEnd_relativeGreendlinger
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : ExtremalArcEndDescentStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  extremalJordan_relativeGreendlinger hoff (extremalArcEnd_extremalJordan_of_descent h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEnd_exists_of_descent
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndRemoved
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndLinked
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndBoth
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEnd_kept_of_countP_eq_zero
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEnd_both_of_removed_eq_zero
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndDescentStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEnd_extremalJordan_of_descent
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEnd_relativeGreendlinger
