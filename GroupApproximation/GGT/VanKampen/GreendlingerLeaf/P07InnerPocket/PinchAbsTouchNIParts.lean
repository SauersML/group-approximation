import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCutStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-76: the NoInterleave / arc split of `pinchCut_Tail`

`pinchCut_Tail b G₁ G₂ outerWalk` (`PinchCutStatement.lean:65`) is a conjunction of eight
clauses.  Clauses 1–4 are `CyclicNoInterleave` facts about the list `invDarts X outerWalk`.
Clauses 5–8 are the arc clauses for `G₁` / `G₂`.  This file splits them into two Props:
* `pinchAbsTouchNI_NIPart b G₁ G₂ outerWalk`: clauses 1–4, verbatim.  This is lane gl-p07-76's
  target.
* `pinchAbsTouchNI_ArcPart G₁ G₂ outerWalk`: clauses 5–8, verbatim.  This is lane gl-p07-77's
  target.

It also defines the block reading `pinchAbsTouchNI_Blocks`, which is lane gl-p07-76's residual.
`PinchAbsTouchNIList.lean` proves `Blocks → NIPart`.

Endpoints:
* `pinchAbsTouchNI_tail_of : NIPart → ArcPart → pinchCut_Tail`;
* `pinchAbsTouchNI_niPart_of_tail` and `pinchAbsTouchNI_arcPart_of_tail`, the two projections;
* `pinchAbsTouchNI_tail_iff : pinchCut_Tail ↔ NIPart ∧ ArcPart`.

The projections show that the split is exact: nothing is lost and nothing is added.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Clauses 1–4 of `pinchCut_Tail`, verbatim**: the four `CyclicNoInterleave` facts. -/
def pinchAbsTouchNI_NIPart (b : RegionCandidate D eps X) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) (outerWalk : List X.toCombMap.Dart) : Prop :=
  FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts)
    (invDarts X outerWalk) ∧
  FourPiece.CyclicNoInterleave
    (fun e => e ∉ invDarts X G₁.darts ∧ e ∈ invDarts X G₂.darts)
    (invDarts X outerWalk) ∧
  FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts ∨
    (e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∈ b.sideFrom i))
    (invDarts X outerWalk) ∧
  FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts ∨
    (e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∉ b.sideFrom i))
    (invDarts X outerWalk)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchNI_NIPart

/-- **Clauses 5–8 of `pinchCut_Tail`, verbatim**: the arc clauses for `G₁` and `G₂`. -/
def pinchAbsTouchNI_ArcPart (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (outerWalk : List X.toCombMap.Dart) : Prop :=
  (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
    (invDarts X outerWalk).rotate m = U ++ V →
    (∀ e ∈ U, e ∈ invDarts X G₁.darts) →
    (∃ e ∈ V, e ∉ invDarts X G₁.darts) →
    ∃ A : CyclicArc (cellDarts X i), U = invDarts X A.darts) ∧
  ((∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts) →
    ∃ (n : ℕ) (A : CyclicArc (cellDarts X i)),
      invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∧
  (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
    (invDarts X outerWalk).rotate m = U ++ V →
    (∀ e ∈ U, e ∈ invDarts X G₂.darts) →
    (∃ e ∈ V, e ∉ invDarts X G₂.darts) →
    ∃ A : CyclicArc (cellDarts X j), U = invDarts X A.darts) ∧
  ((∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₂.darts) →
    ∃ (n : ℕ) (A : CyclicArc (cellDarts X j)),
      invDarts X (outerWalk.rotate n) = invDarts X A.darts)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchNI_ArcPart

/-- **The block reading (lane gl-p07-76's residual).**  Some rotation of `invDarts X outerWalk`
is `U₁ ++ U₂ ++ U₃ ++ U₄`, where:
* `U₁` reverses `G₁`;
* `U₃` reverses `G₂` and is off `G₁`;
* `U₂` and `U₄` reverse neither;
* one of `U₂`, `U₄` reverses only darts of the b far side `b.sideFrom i`, and the other none.

Any block may be empty.  This is the same form as lane gl-p07-17's
`PocketLabelFourBlockStatement`, for the list of `pinchCut_Tail`.

**LOUD: it is STRICTLY STRONGER than `pinchAbsTouchNI_NIPart`.**  The cyclic word `G2 A G1 A`
satisfies all four NoInterleave facts but has no block reading.  Here `A` means off `G₁`, `G₂`
and the b far side. -/
def pinchAbsTouchNI_Blocks (b : RegionCandidate D eps X) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) (outerWalk : List X.toCombMap.Dart) : Prop :=
  ∃ (n : ℕ) (U₁ U₂ U₃ U₄ : List X.toCombMap.Dart),
    (invDarts X outerWalk).rotate n = U₁ ++ U₂ ++ U₃ ++ U₄ ∧
    (∀ e ∈ U₁, e ∈ invDarts X G₁.darts) ∧
    (∀ e ∈ U₃, e ∉ invDarts X G₁.darts ∧ e ∈ invDarts X G₂.darts) ∧
    (∀ e ∈ U₂, e ∉ invDarts X G₁.darts ∧ e ∉ invDarts X G₂.darts) ∧
    (∀ e ∈ U₄, e ∉ invDarts X G₁.darts ∧ e ∉ invDarts X G₂.darts) ∧
    (((∀ e ∈ U₂, X.toCombMap.alpha e ∈ b.sideFrom i) ∧
        ∀ e ∈ U₄, X.toCombMap.alpha e ∉ b.sideFrom i) ∨
      ((∀ e ∈ U₂, X.toCombMap.alpha e ∉ b.sideFrom i) ∧
        ∀ e ∈ U₄, X.toCombMap.alpha e ∈ b.sideFrom i))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchNI_Blocks

/-- **The combination lemma.**  The NoInterleave part and the arc part give `pinchCut_Tail`. -/
theorem pinchAbsTouchNI_tail_of {b : RegionCandidate D eps X} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {outerWalk : List X.toCombMap.Dart}
    (hNI : pinchAbsTouchNI_NIPart b G₁ G₂ outerWalk)
    (hArc : pinchAbsTouchNI_ArcPart G₁ G₂ outerWalk) : pinchCut_Tail b G₁ G₂ outerWalk := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hNI
  obtain ⟨h₅, h₆, h₇, h₈⟩ := hArc
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchNI_tail_of

/-- The tail gives its NoInterleave part. -/
theorem pinchAbsTouchNI_niPart_of_tail {b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {outerWalk : List X.toCombMap.Dart} (h : pinchCut_Tail b G₁ G₂ outerWalk) :
    pinchAbsTouchNI_NIPart b G₁ G₂ outerWalk := by
  obtain ⟨h₁, h₂, h₃, h₄, -, -, -, -⟩ := h
  exact ⟨h₁, h₂, h₃, h₄⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchNI_niPart_of_tail

/-- The tail gives its arc part. -/
theorem pinchAbsTouchNI_arcPart_of_tail {b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {outerWalk : List X.toCombMap.Dart} (h : pinchCut_Tail b G₁ G₂ outerWalk) :
    pinchAbsTouchNI_ArcPart G₁ G₂ outerWalk := by
  obtain ⟨-, -, -, -, h₅, h₆, h₇, h₈⟩ := h
  exact ⟨h₅, h₆, h₇, h₈⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchNI_arcPart_of_tail

/-- **The split is exact.** -/
theorem pinchAbsTouchNI_tail_iff {b : RegionCandidate D eps X} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {outerWalk : List X.toCombMap.Dart} :
    pinchCut_Tail b G₁ G₂ outerWalk ↔
      pinchAbsTouchNI_NIPart b G₁ G₂ outerWalk ∧
        pinchAbsTouchNI_ArcPart G₁ G₂ outerWalk :=
  ⟨fun h => ⟨pinchAbsTouchNI_niPart_of_tail h, pinchAbsTouchNI_arcPart_of_tail h⟩,
    fun h => pinchAbsTouchNI_tail_of h.1 h.2⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchNI_tail_iff

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
