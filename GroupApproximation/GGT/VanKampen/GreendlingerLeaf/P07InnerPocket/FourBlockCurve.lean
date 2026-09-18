import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-22: the priority-filtered pocket curve word

Words for `FourBlock.PocketCurveSublistStatement` (`FourBlockStatement.lean`).  Infrastructure for
Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Certifies no printed sentence on its own.

## The pocket curve

The regions `a` and `b` join the cells `Π_i` and `Π_j`.  The middle of the pocket is bounded by the
closed dart walk `Γ = G₁ · b.sideFrom i · G₂ · a.sideFrom j`:
* `G₁` ends where the arc of `b` on `Π_i` starts, and `b.sideFrom i` starts there;
* `b.sideFrom i` ends where the arc of `b` on `Π_j` ends, which is where `G₂` starts;
* the same holds with `a`, `j`, `i` in place of `b`, `i`, `j`.
Its inverse `invDarts X Γ` is cyclically `Ḡ₁ · Ā · Ḡ₂ · B̄`, where `Ā = invDarts (a.sideFrom j)` and
`B̄ = invDarts (b.sideFrom i)`.

## The priority filter

The classes of `PocketLabelFourBlockStatement` (`NoninterleaveStatement.lean`) are priority
classes: `G1` before `G2` before `B` before `A`.  Each word below keeps only the entries of its
own priority class:
* `cellG2Word`: entries of `Ḡ₂` off `Ḡ₁`;
* `sideBWord`: entries of `B̄` off `Ḡ₁` and `Ḡ₂`;
* `sideAWord`: entries of `Ā` off `Ḡ₁` and `Ḡ₂` whose reverse is off `b.sideFrom i`.
The filter only removes something when a far side runs along `Π_i` or `Π_j`.  That needs a relator
cell inside a region, which is possible only when a contact arc is empty.

The `mem_*` lemmas read the class off a filtered word.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock

universe u w v

open Embedded HullSC WordMetric

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

open scoped Classical in
/-- The `A` block of the pocket curve word: reverses of the far side `a.sideFrom j`, kept when
they are in the priority class `A`. -/
noncomputable def sideAWord (a b : RegionCandidate D eps X) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) : List X.toCombMap.Dart :=
  (invDarts X (a.sideFrom j)).filter fun e => decide (e ∉ invDarts X G₁.darts ∧
    e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∉ b.sideFrom i)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock.sideAWord

open scoped Classical in
/-- The `G2` block of the pocket curve word: `invDarts G₂`, kept off `invDarts G₁`. -/
noncomputable def cellG2Word (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j)) :
    List X.toCombMap.Dart :=
  (invDarts X G₂.darts).filter fun e => decide (e ∉ invDarts X G₁.darts ∧
    e ∈ invDarts X G₂.darts)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock.cellG2Word

open scoped Classical in
/-- The `B` block of the pocket curve word: reverses of the far side `b.sideFrom i`, kept off
`invDarts G₁` and `invDarts G₂`. -/
noncomputable def sideBWord (b : RegionCandidate D eps X) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) : List X.toCombMap.Dart :=
  (invDarts X (b.sideFrom i)).filter fun e => decide (e ∉ invDarts X G₁.darts ∧
    e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∈ b.sideFrom i)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock.sideBWord

/-- An entry of the `A` block is in the priority class `A`. -/
theorem mem_sideAWord {a b : RegionCandidate D eps X} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {e : X.toCombMap.Dart} (he : e ∈ sideAWord a b G₁ G₂) :
    e ∉ invDarts X G₁.darts ∧ e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∉ b.sideFrom i := by
  unfold sideAWord at he
  exact @of_decide_eq_true _ (_) (List.mem_filter.mp he).2

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock.mem_sideAWord

/-- An entry of the `G2` block is in the priority class `G2`. -/
theorem mem_cellG2Word {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {e : X.toCombMap.Dart} (he : e ∈ cellG2Word G₁ G₂) :
    e ∉ invDarts X G₁.darts ∧ e ∈ invDarts X G₂.darts := by
  unfold cellG2Word at he
  exact @of_decide_eq_true _ (_) (List.mem_filter.mp he).2

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock.mem_cellG2Word

/-- An entry of the `B` block is in the priority class `B`. -/
theorem mem_sideBWord {b : RegionCandidate D eps X} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {e : X.toCombMap.Dart} (he : e ∈ sideBWord b G₁ G₂) :
    e ∉ invDarts X G₁.darts ∧ e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∈ b.sideFrom i := by
  unfold sideBWord at he
  exact @of_decide_eq_true _ (_) (List.mem_filter.mp he).2

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock.mem_sideBWord

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock
