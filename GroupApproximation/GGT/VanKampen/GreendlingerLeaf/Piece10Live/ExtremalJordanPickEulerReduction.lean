import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickEuler
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickThreeReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# The Euler core from the counting identity

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-39.

`ExtremalJordanPickThreeTwoOutsideStatement` (lane gl-p10-38) asks for three walk darts that are
pairwise not linked by face classes and first turns.  Its proof sketch
(`Piece10Live/ExtremalJordanPickThree`) has two parts.

* **Local part, proved here.**  `ExtremalJordanPickEulerLocal K` collects five proved facts about
  the rotation at the vertices of the walk (module `Piece10Live/ExtremalJordanPickEuler`).
  - Alternation: from a walk dart, the first kept dart in the rotation is a reversal.
  - First passages are exactly the passages with a free sector.
  - First passages cross no turn.
  - Every non-first passage has a non-first successor at its vertex.
  - The local lemma `n_v ≥ 1 ⇒ n_v ≥ 3`: every non-first passage has two more non-first
    passages at its vertex, pairwise distinct.
  `extremalJordanPickEuler_local` proves it from `K.ClosedWalk` and the rose hypothesis.
* **Global part, left open.**  `ExtremalJordanPickEulerCountStatement` is the TwoOutside statement
  with `ExtremalJordanPickEulerLocal K` as an extra hypothesis.  What remains is the global count
  on the genus-0 walk map: Euler's identity `#linked + #outside = 2 + Σ_v max(n_v - 1, 0)`, and
  the parity argument that rules out one vertex with `n_v = 3` together with exactly two outside
  classes.

**LOUD (strength).**  As a proposition the residual carries one extra hypothesis, so the target
implies it (`extremalJordanPickEuler_count_of_twoOutside`).  That hypothesis is a proved theorem,
so the residual also implies the target (`extremalJordanPickEuler_twoOutside_of_count`).  The two
are therefore EQUIVALENT in logical strength and in truth.  The residual is NOT logically weaker.
It is strictly smaller in proof content: alternation, the characterization of first turns, the
non-crossing of first passages and the local lemma `n_v ≥ 1 ⇒ n_v ≥ 3` are proved and handed to
it, and only the global Euler count and the parity step are left.

**Truth check** (`SP/gl-p10-38/ex7.py`, output `ex7_m6.out`, lane-34 model `configs_b`).

| darts | configurations |
|-------|----------------|
| 3     | 2              |
| 4     | 34             |
| 5     | 506            |
| 6     | 8,468          |

* The identity holds in every instance, with equality.
* Every vertex with `n_v ≥ 1` has `n_v ≥ 3`.
* No instance with at most two outside classes has fewer than three linked classes: 494 instances
  have one outside class and 1,245 have two.
* The two-outside hypothesis is needed: 3,853 instances have three outside classes and fewer than
  three linked classes.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open scoped Classical

section EulerLocal

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Alternation**: from a walk dart `a`, the first kept dart `(σ^k) a` in the rotation is the
reversal of a walk dart. -/
def ExtremalJordanPickEulerAlternates (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∀ a ∈ K.boundary.cycle, ∀ k : ℕ, 0 < k →
    (∀ t, 0 < t → t < k →
      ¬walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) a)) →
    walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ k) a) →
      X.toCombMap.alpha ((X.toCombMap.sigma ^ k) a) ∈ K.boundary.cycle

/-- **First passages**: `d` is a first passage exactly when the sector from `next d` to `α d`
is free. -/
def ExtremalJordanPickEulerFirstIff (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∀ (d : X.toCombMap.Dart) (hd : d ∈ K.boundary.cycle),
    ¬P10ChordLift.NonFirstTurn K d hd ↔
      SectorNoninterleaving.SectorFree X.toCombMap K.boundary.cycle
        (K.boundary.cycle.next d hd) (X.toCombMap.alpha d)

/-- **First passages cross nothing**: both ends of a first passage lie on one side of the
sector of any turn. -/
def ExtremalJordanPickEulerFirstUncrossed (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∀ (d₀ : X.toCombMap.Dart) (hd₀ : d₀ ∈ K.boundary.cycle) (d : X.toCombMap.Dart)
    (hd : d ∈ K.boundary.cycle), ¬P10ChordLift.NonFirstTurn K d hd →
      (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (X.toCombMap.alpha d) ↔
        RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (K.boundary.cycle.next d hd))

/-- **Successors**: every non-first passage `d₀` has a non-first successor `d₁ ≠ d₀` at its
vertex, with a free sector from `next d₀` to `α d₁`. -/
def ExtremalJordanPickEulerNextNonFirst (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∀ (d₀ : X.toCombMap.Dart) (hd₀ : d₀ ∈ K.boundary.cycle),
    P10ChordLift.NonFirstTurn K d₀ hd₀ →
      ∃ (d₁ : X.toCombMap.Dart) (hd₁ : d₁ ∈ K.boundary.cycle), d₁ ≠ d₀ ∧
        P10ChordLift.NonFirstTurn K d₁ hd₁ ∧
        SectorNoninterleaving.SectorFree X.toCombMap K.boundary.cycle
          (K.boundary.cycle.next d₀ hd₀) (X.toCombMap.alpha d₁) ∧
        X.toCombMap.vertexOf (X.toCombMap.alpha d₁) =
          X.toCombMap.vertexOf (X.toCombMap.alpha d₀)

/-- **The local lemma `n_v ≥ 1 ⇒ n_v ≥ 3`**: every non-first passage has two more non-first
passages at its vertex, the three pairwise distinct. -/
def ExtremalJordanPickEulerThreeAtVertex (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∀ (d₀ : X.toCombMap.Dart) (hd₀ : d₀ ∈ K.boundary.cycle),
    P10ChordLift.NonFirstTurn K d₀ hd₀ →
      ∃ (d₁ : X.toCombMap.Dart) (hd₁ : d₁ ∈ K.boundary.cycle) (d₂ : X.toCombMap.Dart)
        (hd₂ : d₂ ∈ K.boundary.cycle),
        P10ChordLift.NonFirstTurn K d₁ hd₁ ∧ P10ChordLift.NonFirstTurn K d₂ hd₂ ∧
          d₁ ≠ d₀ ∧ d₂ ≠ d₀ ∧ d₁ ≠ d₂ ∧
          X.toCombMap.vertexOf (X.toCombMap.alpha d₁) =
            X.toCombMap.vertexOf (X.toCombMap.alpha d₀) ∧
          X.toCombMap.vertexOf (X.toCombMap.alpha d₂) =
            X.toCombMap.vertexOf (X.toCombMap.alpha d₀)

/-- **The local package**: the five local facts together. -/
def ExtremalJordanPickEulerLocal (K : PocketFaceSet D eps X lo hi) : Prop :=
  ExtremalJordanPickEulerAlternates K ∧ ExtremalJordanPickEulerFirstIff K ∧
    ExtremalJordanPickEulerFirstUncrossed K ∧ ExtremalJordanPickEulerNextNonFirst K ∧
    ExtremalJordanPickEulerThreeAtVertex K

end EulerLocal

section EulerLocalProofs

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Alternation holds.** -/
theorem extremalJordanPickEuler_alternates (K : PocketFaceSet D eps X lo hi) :
    ExtremalJordanPickEulerAlternates K := fun _ ha _ hk hfree hkeep =>
  extremalJordanPickEuler_alpha_mem_of_firstKept K.boundary.cycle_mem_iff ha hk hfree hkeep

/-- **First passages are the passages with a free sector.** -/
theorem extremalJordanPickEuler_firstIff (K : PocketFaceSet D eps X lo hi) :
    ExtremalJordanPickEulerFirstIff K := fun _ hd =>
  (not_congr (extremalJordanPickEuler_nonFirst_iff K hd)).trans Classical.not_not

/-- **First passages cross nothing.** -/
theorem extremalJordanPickEuler_firstUncrossed (K : PocketFaceSet D eps X lo hi) :
    ExtremalJordanPickEulerFirstUncrossed K := fun _ hd₀ _ hd h =>
  extremalJordanPickEuler_first_uncrossed K hd₀ hd h

/-- **Every non-first passage has a non-first successor.** -/
theorem extremalJordanPickEuler_nextNonFirst (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) : ExtremalJordanPickEulerNextNonFirst K := fun _ hd₀ hnf =>
  extremalJordanPickEuler_next_nonFirst K hK hd₀ hnf

/-- **The local lemma `n_v ≥ 1 ⇒ n_v ≥ 3` holds.** -/
theorem extremalJordanPickEuler_threeAtVertex (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) (hrose : P10ChordLift.AllNonFirstTurnsCrossed K) :
    ExtremalJordanPickEulerThreeAtVertex K := fun _ hd₀ hnf =>
  extremalJordanPickEuler_three_nonFirst K hK hrose hd₀ hnf

/-- **The local package holds** for a pocket in walk order in the rose configuration. -/
theorem extremalJordanPickEuler_local (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (hrose : P10ChordLift.AllNonFirstTurnsCrossed K) : ExtremalJordanPickEulerLocal K :=
  ⟨extremalJordanPickEuler_alternates K, extremalJordanPickEuler_firstIff K,
    extremalJordanPickEuler_firstUncrossed K, extremalJordanPickEuler_nextNonFirst K hK,
    extremalJordanPickEuler_threeAtVertex K hK hrose⟩

end EulerLocalProofs

/-- **OPEN (lane gl-p10-39): the global Euler count.**  This is
`ExtremalJordanPickThreeTwoOutsideStatement` with the proved local package
`ExtremalJordanPickEulerLocal K` as an extra hypothesis.  What is left is Euler's identity
`#linked + #outside = 2 + Σ_v max(n_v - 1, 0)` on the genus-0 walk map, and the parity step.

LOUD: this is EQUIVALENT in logical strength to the TwoOutside statement
(`extremalJordanPickEuler_twoOutside_of_count`, `extremalJordanPickEuler_count_of_twoOutside`).
It is NOT weaker.  It is strictly smaller in proof content, because the local package is proved
(`extremalJordanPickEuler_local`).  It held on every model instance at 3 to 6 darts
(`SP/gl-p10-38/ex7.py`). -/
def ExtremalJordanPickEulerCountStatement : Prop :=
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
        ∃ r₁ ∈ K.boundary.cycle, ∃ r₂ ∈ K.boundary.cycle, ∃ r₃ ∈ K.boundary.cycle,
          ¬ExtremalJordanPickThreeLinked K r₁ r₂ ∧ ¬ExtremalJordanPickThreeLinked K r₁ r₃ ∧
            ¬ExtremalJordanPickThreeLinked K r₂ r₃

/-- **The endpoint**: the global count gives the TwoOutside statement. -/
theorem extremalJordanPickEuler_twoOutside_of_count
    (h : ExtremalJordanPickEulerCountStatement.{u, w, v}) :
    ExtremalJordanPickThreeTwoOutsideStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose htwo
  exact h D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose htwo
    (extremalJordanPickEuler_local K hK hrose)

/-- **The converse**: the TwoOutside statement gives the global count (so the two are
equivalent). -/
theorem extremalJordanPickEuler_count_of_twoOutside
    (h : ExtremalJordanPickThreeTwoOutsideStatement.{u, w, v}) :
    ExtremalJordanPickEulerCountStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose htwo _
  exact h D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose htwo

/-- **The endpoint for the Three statement**: the global count gives
`ExtremalJordanPickRegionThreeStatement`. -/
theorem extremalJordanPickEuler_three_of_count
    (h : ExtremalJordanPickEulerCountStatement.{u, w, v}) :
    ExtremalJordanPickRegionThreeStatement.{u, w, v} :=
  extremalJordanPickThree_three_of_twoOutside (extremalJordanPickEuler_twoOutside_of_count h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickEulerAlternates
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickEulerFirstIff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickEulerFirstUncrossed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickEulerNextNonFirst
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickEulerThreeAtVertex
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickEulerLocal
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickEuler_alternates
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickEuler_firstIff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickEuler_firstUncrossed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickEuler_nextNonFirst
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickEuler_threeAtVertex
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickEuler_local
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickEulerCountStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickEuler_twoOutside_of_count
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickEuler_count_of_twoOutside
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickEuler_three_of_count
