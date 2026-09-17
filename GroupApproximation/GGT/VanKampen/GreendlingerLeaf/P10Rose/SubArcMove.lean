import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.SubArc
import GroupApproximation.Meta.AxiomGuard

/-!
# The sub-arc region move from a single-region move

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  This module reduces
`RoseRegionMoveSubArcStatement` (module `P10Rose/SubArc`) to `RoseSingleRegionMoveStatement`, where
the colouring flips exactly one region, and proves the reduction
`regionMoveSubArc_of_singleRegionMove`.

## The reduction

Fix a dart `r` and put `z = regionColour r`, `true` exactly on the region of `r` (the class of `r`
for `FaceClassStep M (walkKeep M c)`).

* *Region-constant* (`regionColour_step`): a step joins two darts of the same class.
* *Never both sides* (`regionColour_indep`): if `d ∈ c` and `α d` both lay in the class of `r`,
  then `d` and `α d` would be in one class, so `face d ∈ F ↔ face (α d) ∈ F`
  (`faceOf_mem_iff_of_walkEqvGen`); but `d` is a boundary dart of `F`.
* *Exterior face*: no dart of the exterior face lies in the class of `r`, so `z` vanishes on it and
  `not_mem_flipFaces` keeps it out.
* *Some dart removed* (`movePred_regionColour_eq_false`): a dart `y ∈ c` with `y` or `α y` in the
  class of `r` has a flipped side.

The listing clauses are passed through unchanged.

## Why `RoseSingleRegionMoveStatement` is expected to be true

* *Picture* (docstring of `P10Rose/SubArc`): the edges of `c` form a plane Eulerian graph `Γ`, the
  regions are its faces, two-coloured (`F`-side, other side), and a one-region move deletes the
  facial walk `∂R` of one region `R ≠ R_E`.  Since `∂R` is a directed closed walk, the remaining
  darts are balanced at every vertex; the `Perm` clause lets them be re-listed as a closed walk, so
  the naive "cycle order" filter need not be closed (it is not, for a lake of a 14-dart rose).
* *Flower test*: the move of the `SubArc` docstring flips the single region `{p₂, q₂}`.
* *Search*: a model of the statement (arbitrary plane Eulerian `Γ` with an Euler circuit meeting
  the rose hypotheses, arc darts forbidden in the sides, side darts weighted, the adversarial
  placement `lo = start t₂ = |outerDarts|`, `hi = lo + |t₂|` that only accepts prefixes of `t₂`,
  and relator cells assumed only in the source region and one kept region, so `R` avoids both):
  every rose configuration with at most five walk darts, and about a hundred random ones with six to
  twelve darts (including ones where the cycle-order lake filter is not closed), has a one-region
  move; about two thousand random ones with up to eleven darts have a move.  Both risks of
  `P10Rose/SubArc` (a middle arc block in every extremal region; a wrapping `t₂` losing a prefix)
  were searched for directly and not found.

Not a proof: the planarity argument (an extremal region of the flower meets the arcs only in a
prefix, suffix or whole arc, and its removal leaves short sides) is not formalised.
## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides FilterMove

namespace SubArcMove

/-- **The colouring of one region**: `true` exactly on the face-class of `r`. -/
noncomputable def regionColour (M : CombMap.{v}) (keep : M.Dart → Prop) (r x : M.Dart) : Bool :=
  @ite Bool (Relation.EqvGen (CombMap.FaceClassStep M keep) r x) (Classical.propDecidable _)
    true false

theorem regionColour_eq_true_iff (M : CombMap.{v}) (keep : M.Dart → Prop) (r x : M.Dart) :
    regionColour M keep r x = true ↔ Relation.EqvGen (CombMap.FaceClassStep M keep) r x := by
  unfold regionColour
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩

/-- Two Booleans with the same truth are equal. -/
theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact absurd (h.mpr rfl) (by decide)
  · exact absurd (h.mp rfl) (by decide)
  · rfl

/-- The colouring of one region is constant along the face-class steps. -/
theorem regionColour_step (M : CombMap.{v}) (keep : M.Dart → Prop) (r : M.Dart) :
    ∀ x y, CombMap.FaceClassStep M keep x y →
      regionColour M keep r x = regionColour M keep r y := by
  intro x y hxy
  apply bool_eq_of_iff
  rw [regionColour_eq_true_iff, regionColour_eq_true_iff]
  exact ⟨fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ hxy),
    fun h => Relation.EqvGen.trans _ _ _ h
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hxy))⟩

/-- A dart outside the class of `r` is not flipped. -/
theorem regionColour_eq_false (M : CombMap.{v}) (keep : M.Dart → Prop) {r x : M.Dart}
    (hx : ¬Relation.EqvGen (CombMap.FaceClassStep M keep) r x) :
    regionColour M keep r x = false := by
  cases h : regionColour M keep r x with
  | false => rfl
  | true => exact absurd ((regionColour_eq_true_iff M keep r x).mp h) hx

/-- One region never contains both sides of a dart of the boundary cycle. -/
theorem regionColour_indep {M : CombMap.{v}} {faces : Finset M.Face} {c : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d) (r : M.Dart) :
    ∀ d ∈ c, regionColour M (walkKeep M c) r d = false ∨
      regionColour M (walkKeep M c) r (M.alpha d) = false := by
  intro d hd
  cases h1 : regionColour M (walkKeep M c) r d with
  | false => exact Or.inl rfl
  | true =>
    cases h2 : regionColour M (walkKeep M c) r (M.alpha d) with
    | false => exact Or.inr rfl
    | true =>
      exfalso
      have e1 := (regionColour_eq_true_iff M (walkKeep M c) r d).mp h1
      have e2 := (regionColour_eq_true_iff M (walkKeep M c) r (M.alpha d)).mp h2
      obtain ⟨hin, hout⟩ := (hc d).mp hd
      exact hout ((faceOf_mem_iff_of_walkEqvGen hc
        (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ e1) e2)).mp hin)

/-- A dart with a side in the class of `r` is removed by the move. -/
theorem movePred_regionColour_eq_false {M : CombMap.{v}} {c : List M.Dart} {r y : M.Dart}
    (hy : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r y ∨
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r (M.alpha y)) :
    movePred M (regionColour M (walkKeep M c) r) y = false := by
  cases hp : movePred M (regionColour M (walkKeep M c) r) y with
  | false => rfl
  | true =>
    obtain ⟨h1, h2⟩ := (movePred_eq_true_iff M _ y).mp hp
    rcases hy with hy | hy
    · exact absurd ((regionColour_eq_true_iff M _ r y).mpr hy) (by rw [h1]; decide)
    · exact absurd ((regionColour_eq_true_iff M _ _ _).mpr hy) (by rw [h2]; decide)

end SubArcMove
open SubArcMove

/-- **A single-region move for the rose step** (OPEN; the isolated remaining claim of `P10Rose`).
Under the rose hypotheses, some dart `r` whose region avoids the exterior face and meets a side of a
dart of the cycle gives, with `z = regionColour r`, the listing clauses of
`RoseRegionMoveSubArcStatement`.  See the module docstring for the evidence. -/
def RoseSingleRegionMoveStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ r : X.toCombMap.Dart,
          (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
            (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
          (∃ y ∈ K.boundary.cycle, Relation.EqvGen
            (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r y ∨
            Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
              (walkKeep X.toCombMap K.boundary.cycle)) r (X.toCombMap.alpha y)) ∧
          ∃ (source kept : Fin X.rCellCount),
            (cell X source).face ∉ flipFaces X.toCombMap K.faces
              (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
            (cell X kept).face ∈ flipFaces X.toCombMap K.faces
              (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
            ∃ (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
              (s₁ s₂ : List X.toCombMap.Dart),
              List.Perm (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
                (K.boundary.cycle.filter (movePred X.toCombMap
                  (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))) ∧
              IsClosedDartWalk X.toCombMap (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts) ∧
              s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
              t₂.start.1 + t₂.length ≤ hi ∧
              t₁.length < (cellDarts X source).length ∧ t₂.length < (outerDarts X).length

/-- **The sub-arc region move from a single-region move**: flip the region of `r`. -/
theorem regionMoveSubArc_of_singleRegionMove (h : RoseSingleRegionMoveStatement.{u, w, v}) :
    RoseRegionMoveSubArcStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hrout, ⟨y, hy, hry⟩, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, hwalk,
    hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩ := h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  have hz := regionColour_step X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r
  exact ⟨regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r, hz,
    regionColour_indep K.boundary.cycle_mem_iff r,
    not_mem_flipFaces hz K.outerFace_not_mem
      (fun x hx => regionColour_eq_false X.toCombMap _ (hrout x hx)),
    ⟨y, hy, movePred_regionColour_eq_false hry⟩, source, kept, hsource, hkept, t₁, t₂, s₁, s₂,
    hperm, hwalk, hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩

/-- **The rose step from a single-region move.** -/
theorem rose_of_singleRegionMove (h : RoseSingleRegionMoveStatement.{u, w, v}) :
    P10ChordLift.RoseStepStatement.{u, w, v} :=
  rose_of_regionMoveSubArc (regionMoveSubArc_of_singleRegionMove h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.SubArcMove.regionColour
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.SubArcMove.regionColour_eq_true_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.SubArcMove.bool_eq_of_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.SubArcMove.regionColour_step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.SubArcMove.regionColour_eq_false
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.SubArcMove.regionColour_indep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.SubArcMove.movePred_regionColour_eq_false
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.RoseSingleRegionMoveStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.regionMoveSubArc_of_singleRegionMove
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.rose_of_singleRegionMove
