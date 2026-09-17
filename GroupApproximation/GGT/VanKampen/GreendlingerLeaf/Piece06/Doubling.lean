import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Refinement
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the step at bad corners, through a rotation refinement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Step 5 of the plan in `Piece06/Predicate`
(gap 5).  Let `c = K.boundary.cycle` be the boundary of a cell pocket in walk order, `d₀ → e₀ = next d₀`
an uncrossed non-first turn, and suppose the minimal corners are bad (`¬ GoodTurnCorners X d₀ e₀`).

## Transport across a refinement (`exists_step_of_refinement`, proved)

Let `R : RotationRefinement X X'` (`Piece06/Refinement`), write `e = R.map`, and let `K'` be a cell
pocket of `X'` with `K'.boundary.cycle = c.map e`, the same number of repeated visits, walk order,
distinct cells and proper arcs.  Put `d₀' = e d₀`, `e₀' = e e₀`.

* `d₀' ∈ c'` and `next d₀' = e₀'`, since `e` is injective and `c` has no duplicates
  (`next_map_of_eq`).
* The turn stays non-first: a first turn along `c'.reverse.map α'` from `α' e₀' = e (α e₀)` to
  `α' d₀' = e (α d₀)` is one along `c'` (`FirstTurnWalk.walkKeep_reverse_map_alpha`), i.e. along
  `c.map e`; it projects to a first turn along `c` (`RotationRefinement.firstTurn_of_map`), hence along
  `c.reverse.map α`, contradicting `hnot`.
* The turn stays uncrossed: every `d ∈ c'` is `e b` with `b ∈ c`, `next d = e (next b)`,
  `α' (e b) = e (α b)`, and `SameCycle`, `RotationBetween` between images are those between the old
  darts (`sameCycle_map_iff`, `rotationBetween_map_iff`); this is `huncross` at `b`.
* A sector of `X'` from `e₀'` to `x = σ'^m e₀'`, and from `y` to `σ'^q y = α' d₀'`, all of whose
  intermediate darts are new (outside the range of `e`), avoids the edges of `c' = c.map e`
  (`not_walkKeep_map_of_new`).
* If its corner faces `face (α' x)`, `face (α' y)` are distinct, off the exterior and off the relator
  cells (`RefinedGoodSector`), `Piece06.exists_step_of_goodSector` in `X'` performs the step; the
  O-equivalences compose (`OEquivalentDiscDiagram.trans`) and the repeated visits of `K'` equal
  those of `K`.

## The doubling (`BadCornerRefinementStatement`, the isolated gap)

Write `u = e₀` and `y₀ = σ⁻¹ (α d₀)`; the corner faces are `f = face (α u) = face (σ u)` and
`g = face (α y₀) = face (α d₀)`, both off `K.faces` (they contain `α` of boundary darts).

* Doubling an edge of the corner between `u` and `σ u` (the edge of `α u` or that of `σ u`, both on
  `f`) inserts one new dart at the vertex strictly between `u` and `σ u`, and a G-digon becomes the
  corner face there: `x = e u` with `m = 0`, or `x` the new dart with `m = 1`.  Symmetrically at
  `y₀ → α d₀`: `y = e y₀` with `q = 2`, or `y` the new dart with `q = 1`.  The new darts are not in
  the range of `e`, so the sector hypotheses of `RefinedGoodSector` hold.
* The doubling is `CellPocketFaceSet.faceEdgeDoubling` (G-face or relator-cell face `f ≠ outer`,
  `1 < |f|`), or `CellPocketFaceSet.outerSpurThickening` when `f` is the exterior (`1 < |f|`).  They
  keep walk order, proper arcs and repeated visits (`faceEdgeDoubling_closedWalk`,
  `faceEdgeDoubling_repeatedVisits`, `outerSpurThickening_*`), their boundary cycle is
  `c.map embed` (`faceEdgeDoubling_boundary_cycle`), and their maps are split maps
  `EdgeInsertion.toCombMap` at two distinct corners (`EdgeInsertion.corners_ne`), so
  `RotationRefinement.edgeInsertion` applies, and `RotationRefinement.comp` for the second corner.
* The arc avoidance of `faceEdgeDoubling` fails for both edges of the corner only when `α u` and
  `σ u` are consecutive darts of an arc; then `α (σ u)` precedes `u` in `c`, so `σ e₀ = α d₀` and
  `d₀ → e₀` is a first turn with `k = 1`, which `hnot` excludes (`sigma_ne_alpha_of_not_firstTurn`
  supplies `σ e₀ ≠ α d₀` to the statement).
* The face images are injective, the exterior and the relator cells of `X'` are images of those of
  `X`, and the digon is new; so the two digons are distinct, off the exterior and off the cells.
* **Missing:** a monogon corner face (`|f| = 1`), which is either a relator cell or the exterior,
  admits neither surgery above (`hlen`).  `MonogonDoubling` doubles it, but has no cell-pocket
  transport in the library, and the exterior monogon has no surgery.  Also not yet formalized: the
  rotation of the split map at the corner (which new dart lies between `u` and `σ u`) and the face
  of the new dart.  All of this is `BadCornerRefinementStatement`; `Piece06.exists_step_of_badCorners`
  is proved from it.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated
open scoped Classical

/-- Successors in an image list, through an equation of lists. -/
theorem next_map_of_eq {α β : Type*} {f : α → β} (hf : Function.Injective f) {l : List α}
    {l' : List β} (hl' : l' = l.map f) (hl : l.Nodup) {a : α} (ha : a ∈ l) (hb : f a ∈ l') :
    l'.next (f a) hb = f (l.next a ha) := by
  subst hl'
  exact OuterPinchCornerFix.next_map_of_injective hf hl ha hb

/-- A non-first turn is not the one-step turn: `σ e₀ ≠ α d₀`. -/
theorem sigma_ne_alpha_of_not_firstTurn {M : CombMap.{v}} {c : List M.Dart} {d₀ e₀ : M.Dart}
    (hnot : ¬ FirstTurn M c (M.alpha e₀) (M.alpha d₀)) : M.sigma e₀ ≠ M.alpha d₀ := by
  intro h
  refine hnot ⟨1, Nat.one_pos, ?_, fun t ht ht1 => absurd ht1 (by omega)⟩
  rw [pow_one, M.alpha_involutive e₀]
  exact h

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- **A good sector through a refinement**: from `e e₀` to `x`, and from `y` to `e (α d₀)`, past new
darts only, with corner faces distinct, off the exterior and off the relator cells. -/
def RefinedGoodSector (X X' : DiscDiagram.{u, w, v} W)
    (R : RotationRefinement X.toCombMap X'.toCombMap) (d₀ e₀ : X.toCombMap.Dart) : Prop :=
  ∃ (x y : X'.toCombMap.Dart) (m q : ℕ), (X'.toCombMap.sigma ^ m) (R.map e₀) = x ∧
    (∀ t, 0 < t → t ≤ m → ∀ w, (X'.toCombMap.sigma ^ t) (R.map e₀) ≠ R.map w) ∧ 0 < q ∧
    (X'.toCombMap.sigma ^ q) y = R.map (X.toCombMap.alpha d₀) ∧
    (∀ t, 0 < t → t < q → ∀ w, (X'.toCombMap.sigma ^ t) y ≠ R.map w) ∧
    X'.toCombMap.faceOf (X'.toCombMap.alpha x) ≠ X'.toCombMap.faceOf (X'.toCombMap.alpha y) ∧
    X'.toCombMap.faceOf (X'.toCombMap.alpha x) ≠ X'.outerFace ∧
    X'.toCombMap.faceOf (X'.toCombMap.alpha y) ≠ X'.outerFace ∧
    (∀ C ∈ X'.relatorCells, C.face ≠ X'.toCombMap.faceOf (X'.toCombMap.alpha x)) ∧
    ∀ C ∈ X'.relatorCells, C.face ≠ X'.toCombMap.faceOf (X'.toCombMap.alpha y)

section Transport

variable {X X' : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount} {i' j' : Fin X'.rCellCount}
  (K : CellPocketFaceSet D eps X i j) (K' : CellPocketFaceSet D eps X' i' j')
  (R : RotationRefinement X.toCombMap X'.toCombMap)

/-- The turn stays non-first across a refinement. -/
theorem not_firstTurn_of_refinement (hcycle : K'.boundary.cycle = K.boundary.cycle.map R.map)
    {d₀ e₀ : X.toCombMap.Dart}
    (hnot : ¬ FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
      (X.toCombMap.alpha e₀) (X.toCombMap.alpha d₀)) :
    ¬ FirstTurn X'.toCombMap (K'.boundary.cycle.reverse.map X'.toCombMap.alpha)
      (X'.toCombMap.alpha (R.map e₀)) (X'.toCombMap.alpha (R.map d₀)) := by
  intro h
  rw [R.alpha_map, R.alpha_map] at h
  have h₁ : FirstTurn X'.toCombMap (K.boundary.cycle.map R.map)
      (R.map (X.toCombMap.alpha e₀)) (R.map (X.toCombMap.alpha d₀)) :=
    FirstTurn.mono (fun z hz => by
      rw [FirstTurnWalk.walkKeep_reverse_map_alpha, hcycle]
      exact hz) h
  have h₂ := R.firstTurn_of_map h₁
  exact hnot (FirstTurn.mono (fun z hz => by
    rwa [FirstTurnWalk.walkKeep_reverse_map_alpha] at hz) h₂)

/-- The turn stays uncrossed across a refinement. -/
theorem huncross_of_refinement (hcycle : K'.boundary.cycle = K.boundary.cycle.map R.map)
    {d₀ e₀ : X.toCombMap.Dart}
    (huncross : ∀ d (hd : d ∈ K.boundary.cycle), d ≠ d₀ →
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) →
        (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (X.toCombMap.alpha d) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (K.boundary.cycle.next d hd))) :
    ∀ d (hd : d ∈ K'.boundary.cycle), d ≠ R.map d₀ →
      X'.toCombMap.sigma.SameCycle (X'.toCombMap.alpha (R.map d₀)) (X'.toCombMap.alpha d) →
        (RotationBetween X'.toCombMap (X'.toCombMap.alpha (R.map d₀)) (R.map e₀)
            (X'.toCombMap.alpha d) ↔
          RotationBetween X'.toCombMap (X'.toCombMap.alpha (R.map d₀)) (R.map e₀)
            (K'.boundary.cycle.next d hd)) := by
  intro d hd hdne hsame
  have hd₁ := hd
  rw [hcycle] at hd₁
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hd₁
  rw [R.alpha_map, R.alpha_map, R.sameCycle_map_iff] at hsame
  rw [next_map_of_eq R.injective hcycle K.boundary.cycle_nodup hb hd, R.alpha_map, R.alpha_map,
    R.rotationBetween_map_iff, R.rotationBetween_map_iff]
  exact huncross b hb (fun h => hdne (by rw [h])) hsame

/-- **One step of the cell pinch through a rotation refinement with a good refined sector.** -/
theorem exists_step_of_refinement (hE : Nonempty (OEquivalentDiscDiagram X X'))
    (hlabel' : ∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) (hij' : i' ≠ j')
    (hK' : K'.ClosedWalk) (hfirst' : K'.firstArc.length < (cellDarts X' i').length)
    (hsecond' : K'.secondArc.length < (cellDarts X' j').length)
    (hvisits : K'.repeatedVisits = K.repeatedVisits)
    (hcycle : K'.boundary.cycle = K.boundary.cycle.map R.map)
    {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle)
    (hnext₀ : K.boundary.cycle.next d₀ hd₀ = e₀)
    (hnot : ¬ FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
      (X.toCombMap.alpha e₀) (X.toCombMap.alpha d₀))
    (huncross : ∀ d (hd : d ∈ K.boundary.cycle), d ≠ d₀ →
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) →
        (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (X.toCombMap.alpha d) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (K.boundary.cycle.next d hd)))
    (hsector : RefinedGoodSector X X' R d₀ e₀) :
    ∃ (X'' : DiscDiagram.{u, w, v} W) (i'' j'' : Fin X''.rCellCount)
      (K'' : CellPocketFaceSet D eps X'' i'' j''),
      Nonempty (OEquivalentDiscDiagram X X'') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X''.label d)) ∧ i'' ≠ j'' ∧
        K''.ClosedWalk ∧ K''.firstArc.length < (cellDarts X'' i'').length ∧
        K''.secondArc.length < (cellDarts X'' j'').length ∧
        K''.repeatedVisits < K.repeatedVisits := by
  obtain ⟨x, y, m, q, hm, hnewm, hq0, hq, hnewq, hne, hxout, hyout, hxcell, hycell⟩ := hsector
  have hd₀' : R.map d₀ ∈ K'.boundary.cycle := by
    rw [hcycle]
    exact R.mem_map_iff.mpr hd₀
  have hnext' : K'.boundary.cycle.next (R.map d₀) hd₀' = R.map e₀ := by
    rw [next_map_of_eq R.injective hcycle K.boundary.cycle_nodup hd₀ hd₀', hnext₀]
  have hkeepm : ∀ t, 0 < t → t ≤ m →
      ¬ walkKeep X'.toCombMap K'.boundary.cycle ((X'.toCombMap.sigma ^ t) (R.map e₀)) := by
    intro t ht htm
    rw [hcycle]
    exact R.not_walkKeep_map_of_new _ (hnewm t ht htm)
  have hkeepq : ∀ t, 0 < t → t < q →
      ¬ walkKeep X'.toCombMap K'.boundary.cycle ((X'.toCombMap.sigma ^ t) y) := by
    intro t ht htq
    rw [hcycle]
    exact R.not_walkKeep_map_of_new _ (hnewq t ht htq)
  have hq' : (X'.toCombMap.sigma ^ q) y = X'.toCombMap.alpha (R.map d₀) := by
    rw [R.alpha_map]
    exact hq
  obtain ⟨X'', i'', j'', K'', ⟨e₂⟩, hlabel'', hij'', hK'', hfirst'', hsecond'', hlt⟩ :=
    exists_step_of_goodSector hlabel' K' hK' hij' hfirst' hsecond' hd₀' hnext'
      (not_firstTurn_of_refinement K K' R hcycle hnot) (huncross_of_refinement K K' R hcycle huncross)
      hm hkeepm hq0 hq' hkeepq hne hxout hyout hxcell hycell
  obtain ⟨e₁⟩ := hE
  exact ⟨X'', i'', j'', K'', ⟨OEquivalentDiscDiagram.trans e₁ e₂⟩, hlabel'', hij'', hK'', hfirst'',
    hsecond'', lt_of_lt_of_eq hlt hvisits⟩

end Transport

/-- **The corner doubling at a non-one-step turn** (gap 5 of `Piece06/Predicate`, isolated).  Some
refinement of the diagram carries the cell pocket, with the same walk order, proper arcs and repeated
visits, and a good refined sector at the turn `d₀ → e₀`.  See the module docstring: the digon and
outer-spur cases follow from `faceEdgeDoubling` and `outerSpurThickening`; monogon corner faces are
not covered by the library. -/
def BadCornerRefinementStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}
    (K : CellPocketFaceSet D eps X i j),
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) → K.ClosedWalk → i ≠ j →
    K.firstArc.length < (cellDarts X i).length → K.secondArc.length < (cellDarts X j).length →
    ∀ {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle),
      K.boundary.cycle.next d₀ hd₀ = e₀ → X.toCombMap.sigma e₀ ≠ X.toCombMap.alpha d₀ →
      ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
        (K' : CellPocketFaceSet D eps X' i' j') (R : RotationRefinement X.toCombMap X'.toCombMap),
        Nonempty (OEquivalentDiscDiagram X X') ∧
          (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
          K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
          K'.secondArc.length < (cellDarts X' j').length ∧
          K'.repeatedVisits = K.repeatedVisits ∧ K'.boundary.cycle = K.boundary.cycle.map R.map ∧
          RefinedGoodSector X X' R d₀ e₀

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.next_map_of_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.sigma_ne_alpha_of_not_firstTurn
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.not_firstTurn_of_refinement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.huncross_of_refinement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.exists_step_of_refinement
