import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.Reduction
import GroupApproximation.Meta.AxiomGuard

/-!
# The rose region move: the witness class meets the walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-10.

The endpoint `Piece10.proof_of_regionMoveSubArc : P10Rose.RoseRegionMoveSubArcStatement →
PocketOuterPinchStepSectionStatement` already exists (module `P10RoseEndpoint/SingleRegion`), so
this module does not state it again.  It works on the gap below it.

## Route

`RoseExtremalCoreStatement` → (`extremalJunction_of_extremalCore`, proved)
`P10RoseExtremalTrim.RoseExtremalJunctionStatement` → `RoseExtremalRegionStatement` →
`RoseSingleRegionMoveStatement` → `RoseRegionMoveSubArcStatement` → `RoseStepStatement` →
`PocketOuterPinchStepSectionStatement` (`Piece10.proof_of_extremalCore`).

* `exists_walkKeep_of_connected` (proved): in a connected map, with `c ≠ []`, every class of
  `FaceClassStep M (walkKeep M c)` contains a dart `x` with `x ∈ c` or `α x ∈ c`.
  *Proof.*  Suppose the class `S` of `r` has no such dart.  Then `S` is closed under `α` (an
  `α`-step is allowed off `walkKeep`) and under `facePerm`.  Since `facePerm (α x) = σ x`, it is
  also closed under `σ`, and each `Adjacent` step can be undone inside `S` (`d = α (α d)`, and
  `σ d ∈ S` gives `α d ∈ S` by a backward face step, then `d ∈ S`).  So `S` is a union of
  `EqvGen Adjacent`-classes, hence all darts (connectedness, `DiscDiagram.planar`).  In particular
  `c.head ∈ S`, and `c.head ∈ c`.  This is a contradiction.
* `exists_mem_eqvGen_of_connected` (proved): the second clause of the junction statement,
  `∃ y ∈ c, r ~ y ∨ r ~ α y`, holds for EVERY dart `r`.
* `RoseExtremalCoreStatement` (OPEN, PLAUSIBLE): `RoseExtremalJunctionStatement` without that
  clause.
* `extremalCore_of_extremalJunction` (proved): the converse, so the residual is exactly as plausible
  as the old gap (truth certificate).

## Why the residual is strictly smaller in proof content, and true when the old one is

It asks for the same witness `r`, cells, arcs and sides, but not for a dart of the cycle touching
the class of `r`.  That clause is now proved for every `r` from connectedness alone.  It is not a
restatement: a proof of the old gap had to produce this clause, and the residual does not.  The
converse (`extremalCore_of_extremalJunction`) shows that the residual is true whenever the old gap
is.

## Truth check on a small model (no counterexample, PLAUSIBLE)

Let `c` be the rose boundary cycle, seen as a plane Eulerian graph of walk darts.

1. *Alternation.*  Around a vertex, in-darts and out-darts of `c` alternate, because membership
   in `F` flips across each dart of `c`.  A vertex of `c`-degree `2` or `4` carries no crossed
   passage.  A crossed non-first turn needs at least three passages at one vertex.
2. *Corners of the arcs.*  A passage inside `t₂` (inside `t₁⁻¹`) runs through a corner of the
   exterior face (of the source cell).  That side contains no walk dart, so the passage is not
   crossed.  Crossed turns occur only at side or junction passages.  With `ε = 0` the sides are
   empty and `AllNonFirstTurnsCrossed K` together with `¬ K.FirstTurns` is contradictory, so the
   statement holds vacuously.
3. *Three-petal flower.*  `c = p₁ q₁ | t₁⁻¹ | p₃ | t₂`, with the petals meeting at one vertex of
   `c`-degree `6`.  The class of the petal region is the witness `r`: `s₁ = [p₃]`, `t₁' = t₁`,
   `s₂ = [p₁, q₁]`, `t₂' = zeroArc t₂`, and the class meets no exterior dart.
4. *Search.*  The exhaustive search on rose configurations with at most five walk darts (542
   configurations, re-run for this lane, none bad) and random configurations with six to twelve
   darts found no counterexample (docstring of `P10RoseEndpoint/SingleRegion`).

The remaining content is the planarity core described in `P10RoseExtremalTrim/Reduction`: the
extremal region meets the arcs in contiguous blocks, and the sides have length at most `ε`.  The
other clauses cannot be derived from the flip-move API.  The first clause (the class avoids the
exterior face) is the extremality choice.  The bounds `lo`, `hi` and properness depend on the
position of the chosen region.  The kept cell cannot be read off a boundary dart of the new face
set, because an inner face of a `DiscDiagram` need not be a relator cell (`DiscDiagram.inner_face`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **Every face class meets the walk** in a connected map: some dart of the class of `r` lies on
`c` or has its reverse on `c`. -/
theorem exists_walkKeep_of_connected {M : CombMap.{v}} (hM : M.IsConnected) {c : List M.Dart}
    (hc : c ≠ []) (r : M.Dart) :
    ∃ x, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r x ∧ walkKeep M c x := by
  by_contra hno
  have hnk : ∀ x, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r x →
      ¬walkKeep M c x :=
    fun x hx hk => hno ⟨x, hx, hk⟩
  have hstep : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y →
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r x →
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r y :=
    fun x y hxy hx => Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.rel _ _ hxy)
  have hback : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y →
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r y →
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r x :=
    fun x y hxy hy =>
      Relation.EqvGen.trans _ _ _ hy (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hxy))
  have halpha : ∀ x, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r x →
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r (M.alpha x) :=
    fun x hx => hstep x (M.alpha x) (Or.inr ⟨hnk x hx, rfl⟩) hx
  have hsig : ∀ x, M.sigma x = M.facePerm (M.alpha x) := by
    intro x
    rw [CombMap.facePerm, Equiv.Perm.mul_apply, M.alpha_involutive x]
  have hall : ∀ d e, Relation.EqvGen M.Adjacent d e →
      (Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r d ↔
        Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r e) := by
    intro d e hde
    induction hde with
    | rel a b hab =>
      rcases (show M.alpha a = b ∨ M.sigma a = b from hab) with rfl | rfl
      · refine ⟨halpha a, fun hb => ?_⟩
        have h2 := halpha _ hb
        rwa [M.alpha_involutive a] at h2
      · have hfs : CombMap.FaceClassStep M (walkKeep M c) (M.alpha a) (M.sigma a) :=
          Or.inl (hsig a)
        refine ⟨fun ha => hstep (M.alpha a) (M.sigma a) hfs (halpha a ha), fun hb => ?_⟩
        have h2 := halpha (M.alpha a) (hback (M.alpha a) (M.sigma a) hfs hb)
        rwa [M.alpha_involutive a] at h2
    | refl _ => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hhead := (hall r (c.head hc) (hM r (c.head hc))).mp (Relation.EqvGen.refl r)
  exact hnk _ hhead (Or.inl (List.head_mem hc))

/-- **The second clause of the junction statement holds for every dart** in a connected map. -/
theorem exists_mem_eqvGen_of_connected {M : CombMap.{v}} (hM : M.IsConnected)
    {c : List M.Dart} (hc : c ≠ []) (r : M.Dart) :
    ∃ y ∈ c, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r y ∨
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r (M.alpha y) := by
  obtain ⟨x, hx, hk⟩ := exists_walkKeep_of_connected hM hc r
  rcases (show x ∈ c ∨ M.alpha x ∈ c from hk) with hk | hk
  · exact ⟨x, hk, Or.inl hx⟩
  · refine ⟨M.alpha x, hk, Or.inr ?_⟩
    rwa [M.alpha_involutive x]

-- LOUD: REFUTED (lane gl-p10-48; Python model, not yet in Lean).
-- `RoseExtremalCoreStatement` is FALSE:
-- it implies `RoseExtremalJunctionStatement`, which fails on the gl-p10-40 G-face model with
-- the label-1 edges subdivided once (24 darts).  Corrected residual:
-- `P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement` (`JunctionCore.lean`).
/-- **The extremal-region core** (OPEN, PLAUSIBLE; the isolated planarity core of the rose step).
`P10RoseExtremalTrim.RoseExtremalJunctionStatement` without the clause "some dart of the cycle, or
its reverse, lies in the class of `r`", which `exists_mem_eqvGen_of_connected` proves. -/
def RoseExtremalCoreStatement : Prop :=
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
              s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts ≠ [] ∧
              (s₁.IsChain fun d e =>
                X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
              (s₂.IsChain fun d e =>
                X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
              (∀ a ∈ s₁.getLast?, ∀ b ∈ (invDarts X t₁.darts).head?,
                X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
              (∀ a ∈ (s₁ ++ invDarts X t₁.darts).getLast?, ∀ b ∈ s₂.head?,
                X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
              (∀ a ∈ (s₁ ++ invDarts X t₁.darts ++ s₂).getLast?, ∀ b ∈ t₂.darts.head?,
                X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
              s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
              t₂.start.1 + t₂.length ≤ hi ∧
              t₁.length < (cellDarts X source).length ∧ t₂.length < (outerDarts X).length

/-- **The junction witness from the core**: the dropped clause holds by connectedness. -/
theorem extremalJunction_of_extremalCore (h : RoseExtremalCoreStatement.{u, w, v}) :
    P10RoseExtremalTrim.RoseExtremalJunctionStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hrout, hrest⟩ := h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨r, hrout, exists_mem_eqvGen_of_connected
    (CombMap.connected_of_planar X.toCombMap X.planar) K.boundary.cycle_nonempty r, hrest⟩

/-- **The core is implied by the junction witness** (truth certificate of the residual). -/
theorem extremalCore_of_extremalJunction
    (h : P10RoseExtremalTrim.RoseExtremalJunctionStatement.{u, w, v}) :
    RoseExtremalCoreStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hrout, -, hrest⟩ := h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨r, hrout, hrest⟩

/-- **The rose step from the extremal-region core.** -/
theorem rose_of_extremalCore (h : RoseExtremalCoreStatement.{u, w, v}) :
    P10ChordLift.RoseStepStatement.{u, w, v} :=
  P10RoseExtremalTrim.rose_of_junction (extremalJunction_of_extremalCore h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

universe u w v

/-- **The outer-pinch step from the extremal-region core.** -/
theorem proof_of_extremalCore (h : P10RegionMove.RoseExtremalCoreStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  proof_of_extremalJunction (P10RegionMove.extremalJunction_of_extremalCore h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.exists_walkKeep_of_connected
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.exists_mem_eqvGen_of_connected
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.RoseExtremalCoreStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.extremalJunction_of_extremalCore
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.extremalCore_of_extremalJunction
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.rose_of_extremalCore
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.proof_of_extremalCore
