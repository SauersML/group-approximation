import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCountParity
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCountParityPerm
import GroupApproximation.Meta.AxiomGuard

/-!
# The parity clause: reduction to the orbit count of the face permutation

Lane gl-p10-43.  This file assembles the parity half of `ExtremalJordanPickCountEulerStatement`.

**What is proved.**  Let `f = extremalJordanPickCountParity_perm K`: `α ∘ σ_P` on walk darts,
and the identity elsewhere.  The first-passage law holds: `f (next d) = d` exactly when `d` is a
first passage.  So `f * c.formPerm` moves exactly the non-first passages.  When the excess is
two there are three of them, and it is a 3-cycle, which is even.  The walk permutation
`c.formPerm` is an `L`-cycle.  So the orbit count `L - #supp f + #cycles f` of `f` on the walk
is odd, and `#O ≠ 2` follows once `#O` has the parity of that orbit count.

**The isolated Statement** `ExtremalJordanPickCountParityCyclesStatement`.  Under the premises of
`ExtremalJordanPickCountEulerStatement`, `#O ≡ L - #supp f + #cycles f (mod 2)` for this concrete
`f`.  LOUD: this is logically STRONGER than the parity clause.  It holds for every excess, not
only for excess two, and it names a concrete `f`.  It implies the parity clause
(`extremalJordanPickCountParity_parity`) but is not implied by it.  It is strictly smaller in
proof content: the sign argument, the count of three non-first passages, the construction of `f`
and its first-passage law are all proved.  What remains is face-class bookkeeping.  Each outside
face class is one orbit of `f` on the walk (on the model, `#O` equals the orbit count).

A weaker form would restate the target.  One could quantify over `f`, or keep the hypothesis
`excess = 2`.  Then the residual is the parity clause together with the proved facts above, which
is close to an equivalent restatement.  So the concrete, unconditional form was chosen.

**Truth check** (`SP/gl-p10-43/chk.py`, output `chk_m7.out`).  The model is the lane-34 model
`configs_b`, with up to 7 darts and degree up to 5.  There are 18,837 instances, 6,232 of them
with excess two.  The checker found zero failures of four claims:
* `#O` equals the orbit count of `f`, so the residual holds for every excess;
* `f (next d) = d` exactly for first passages;
* excess two gives three non-first passages;
* excess two gives an odd `#O`.

**The Bound half.**  Lane gl-p10-42 owns Euler's bound.  No interface for it exists in the
repository.  So it is stated here as `ExtremalJordanPickCountParityBoundStatement`.  The endpoint
`extremalJordanPickCountParity_count_of_bound` composes both halves with
`extremalJordanPickCount_count_of_euler`.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open scoped Classical

section ParityCycles

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The orbit-count parity law**: `#O` has the parity of the orbit count
`L - #supp f + #cycles f` of the face permutation `f` on the walk. -/
def ExtremalJordanPickCountParityCycles (K : PocketFaceSet D eps X lo hi) : Prop :=
  (extremalJordanPickCount_outside K).card % 2 =
    (K.boundary.cycle.length - (extremalJordanPickCountParity_perm K).support.card +
      (extremalJordanPickCountParity_perm K).cycleType.card) % 2

/-- **The per-pocket reduction**: the orbit-count parity law gives the parity clause. -/
theorem extremalJordanPickCountParity_of_cycles (K : PocketFaceSet D eps X lo hi)
    (h3 : ExtremalJordanPickEulerThreeAtVertex K) (h : ExtremalJordanPickCountParityCycles K) :
    ExtremalJordanPickCountParity K :=
  extremalJordanPickCountParity_of_perm K h3 (extremalJordanPickCountParity_perm K)
    (extremalJordanPickCountParity_perm_of_not_mem K)
    (extremalJordanPickCountParity_perm_next_iff K) h

end ParityCycles

/-- **OPEN (lane gl-p10-43): the orbit-count parity law.**  Under the premises of
`ExtremalJordanPickCountEulerStatement`, `#O` has the parity of the orbit count of the face
permutation on the walk.  LOUD: this is logically STRONGER than
`ExtremalJordanPickCountParityStatement`, since it holds for every excess and names a concrete
permutation.  It is strictly smaller in proof content.  It held on all 18,837 model instances up
to 7 darts (`SP/gl-p10-43/chk.py`). -/
def ExtremalJordanPickCountParityCyclesStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
      ExtremalJordanPickThreeTwoOutside K →
      ExtremalJordanPickEulerLocal K →
        ExtremalJordanPickCountParityCycles K

/-- **The parity half**: under the premises of `ExtremalJordanPickCountEulerStatement`, the
parity clause `excess = 2 → #O ≠ 2` holds. -/
def ExtremalJordanPickCountParityStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
      ExtremalJordanPickThreeTwoOutside K →
      ExtremalJordanPickEulerLocal K →
        ExtremalJordanPickCountParity K

/-- **The Bound half (interface for lane gl-p10-42)**: under the same premises, Euler's bound
`2 + excess ≤ #L + #O` holds. -/
def ExtremalJordanPickCountParityBoundStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
      ExtremalJordanPickThreeTwoOutside K →
      ExtremalJordanPickEulerLocal K →
        ExtremalJordanPickCountEulerBound K

/-- **The parity half, proved from the orbit-count parity law.** -/
theorem extremalJordanPickCountParity_parity
    (h : ExtremalJordanPickCountParityCyclesStatement.{u, w, v}) :
    ExtremalJordanPickCountParityStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose htwo hloc
  exact extremalJordanPickCountParity_of_cycles K hloc.2.2.2.2
    (h D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose htwo hloc)

/-- **Both halves**: the Bound half and the orbit-count parity law give the class count. -/
theorem extremalJordanPickCountParity_euler_of_bound
    (hb : ExtremalJordanPickCountParityBoundStatement.{u, w, v})
    (hc : ExtremalJordanPickCountParityCyclesStatement.{u, w, v}) :
    ExtremalJordanPickCountEulerStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose htwo hloc
  exact ⟨hb D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose htwo hloc,
    extremalJordanPickCountParity_parity hc D eps X lo hi hhi hla hlabel K hK hft hsrc htgt
      hpin hrose htwo hloc⟩

/-- **The endpoint**: the Bound half and the orbit-count parity law give the global Euler count
statement, through `extremalJordanPickCount_count_of_euler`. -/
theorem extremalJordanPickCountParity_count_of_bound
    (hb : ExtremalJordanPickCountParityBoundStatement.{u, w, v})
    (hc : ExtremalJordanPickCountParityCyclesStatement.{u, w, v}) :
    ExtremalJordanPickEulerCountStatement.{u, w, v} :=
  extremalJordanPickCount_count_of_euler (extremalJordanPickCountParity_euler_of_bound hb hc)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickCountParityCycles
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_of_cycles
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickCountParityCyclesStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickCountParityStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickCountParityBoundStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_parity
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_euler_of_bound
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_count_of_bound
