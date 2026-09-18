import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AssemblyResidual
import GroupApproximation.Meta.AxiomGuard

/-!
# The rose step from the removal of an inside lobe

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-48.

## LOUD: `RoseExtremalJunctionStatement` is FALSE

`P10RoseExtremalTrim.RoseExtremalJunctionStatement` (module `P10RoseExtremalTrim/Reduction`) is
FALSE.  So are `P10RoseExtremal.RoseExtremalRegionStatement` (equivalent to it by
`extremalRegion_of_junction` and `junction_of_extremalRegion`),
`P10Rose.RoseSingleRegionMoveStatement` (its closed-walk listing gives the junctions), and every
Statement that implies one of them, e.g. `P10RegionMove.RoseExtremalCoreStatement`
(`extremalJunction_of_extremalCore`).  The live root
`AssemblyResidual.relativeGreendlinger_of_residuals` therefore rests on a false binder.

*Counterexample (Python evaluation, not formalised).*  Take the G-face model of gl-p10-40
(`Piece10Live/ExtremalJordanPickClsDiagram`, group `Perm (Fin 3)`, `ε = 1`), and subdivide each
of the edges `{2,3}, {6,7}, {8,9}, {12,13}` once: `24` darts, `α d = d xor 1`, the new edges carry
the letter `1`, the relator set gets the longer word of `S`.  Then
`c = [0,2,16,4,6,18,8,20,10,12,22]`, the pocket faces are `f₀ = [0]` (kept cell `K₀`),
`f₂ = [2,16,6,18]`, `f₃ = [4]`, `f₄ = [8,20,12,22]`, `f₆ = [10]`, the source cell is
`S = [1,19,7,5,17,3,14]`, the exterior is `[8,20,10,12,22,14]`, and
`c = [0] ++ [2,16,4,6,18] ++ [] ++ [8,20,10,12,22]` with `t₁ = [19,7,5,17,3]`.  All premises
hold: Euler characteristic `2`, boundary darts `= c`, closed walk, non-first turns `[0,18,22]` all
crossed, every label a letter, least area by the sign argument of the base model (relators odd,
boundary value even and `≠ 1`).  The walk classes are `{0}`, `{2,6,16,18}`, `{4}`,
`{8,12,20,22}`, `{10}` and one outside class that contains the exterior dart `15`.  The exhaustive
evaluator of gl-p10-46 finds `0` witnesses (also with `hi = |exterior|`, for two subdivisions at
`ε = 1, 2` and three at `ε = 2`); the base model has `22` to `24`.  By hand: `{0}` removes the kept
cell, `{4}` and `{10}` break a junction or a length bound, `{2,6,16,18}` breaks a junction, and
`{8,12,20,22}` disconnects the new boundary.

## The corrected residual: remove a whole lobe

On the counterexample the lobe `{2,6,16,18} ∪ {4}`, the two inside classes with roots `2` and `4`
on `c`, works for `RoseRegionMoveSubArcStatement`: `F' = {f₀, f₄, f₆}`, the kept cycle is
`[0,8,20,10,12,22]`, source `S`, kept `K₀`, `t₁ = [1]`, `t₂ = [8,20,10,12,22]`, `s₁ = s₂ = []`,
and the listing is a closed walk.  A search over all sets of inside classes rooted on `c` finds
closed-walk witnesses on the base model (`150` at `ε = 1`) and on one, two and three
subdivisions (`176`, `256` at `ε = 1`; `597` at two, `717` at three subdivisions with `ε = 2`);
on the subdivided models none of them is a single class (lobes of two to four classes).

* `roseJunctionCore_lobeColour` and its API (all proved): the colouring `true` exactly on the
  union of the walk classes of a list of roots; it is region-constant, reduces to `regionColour`
  for one root, and for roots on `c` it never colours a dart outside the face set, so it never
  flips both sides of a cycle dart, keeps the exterior and every outside face out, and removes
  each root.
* `roseJunctionCore_LobeRemovalStatement` (OPEN, PLAUSIBLE): the listing clauses of
  `RoseRegionMoveSubArcStatement` for `z = lobeColour rs`, where either `rs` is a nonempty list
  of cycle darts (a union of inside classes: `F' ⊆ F`, Osin's subdiagram `Γ_1`), or `rs = [r]`
  with the side conditions of `RoseSingleRegionMoveStatement`.
* `roseJunctionCore_regionMoveSubArc_of_lobeRemoval` (proved): the residual gives
  `P10Rose.RoseRegionMoveSubArcStatement`, hence the rose step, the outer-pinch step and, with
  `PocketFourPieceOffStatement`, the Greendlinger leaf
  (`roseJunctionCore_relativeGreendlinger_of_lobeRemoval`, a drop-in replacement for
  `AssemblyResidual.relativeGreendlinger_of_residuals`).
* `roseJunctionCore_lobeRemoval_of_singleRegionMove`, `roseJunctionCore_lobeRemoval_of_junction`
  (proved): the residual is implied by the old targets, so it is weaker than
  `RoseExtremalJunctionStatement`; strictly weaker, since it holds on the counterexample.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **The colouring of a lobe**: `true` exactly on the union of the face classes of the roots. -/
noncomputable def roseJunctionCore_lobeColour (M : CombMap.{v}) (keep : M.Dart → Prop)
    (rs : List M.Dart) (x : M.Dart) : Bool :=
  @ite Bool (∃ r ∈ rs, Relation.EqvGen (CombMap.FaceClassStep M keep) r x)
    (Classical.propDecidable _) true false

theorem roseJunctionCore_lobeColour_eq_true_iff (M : CombMap.{v}) (keep : M.Dart → Prop)
    (rs : List M.Dart) (x : M.Dart) :
    roseJunctionCore_lobeColour M keep rs x = true ↔
      ∃ r ∈ rs, Relation.EqvGen (CombMap.FaceClassStep M keep) r x := by
  unfold roseJunctionCore_lobeColour
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩

/-- A dart outside every root class is not coloured. -/
theorem roseJunctionCore_lobeColour_eq_false (M : CombMap.{v}) (keep : M.Dart → Prop)
    {rs : List M.Dart} {x : M.Dart}
    (hx : ∀ r ∈ rs, ¬Relation.EqvGen (CombMap.FaceClassStep M keep) r x) :
    roseJunctionCore_lobeColour M keep rs x = false := by
  cases h : roseJunctionCore_lobeColour M keep rs x with
  | false => rfl
  | true =>
    obtain ⟨r, hr, hrx⟩ := (roseJunctionCore_lobeColour_eq_true_iff M keep rs x).mp h
    exact absurd hrx (hx r hr)

/-- The colouring of a lobe is constant along the face-class steps. -/
theorem roseJunctionCore_lobeColour_step (M : CombMap.{v}) (keep : M.Dart → Prop)
    (rs : List M.Dart) :
    ∀ x y, CombMap.FaceClassStep M keep x y →
      roseJunctionCore_lobeColour M keep rs x = roseJunctionCore_lobeColour M keep rs y := by
  intro x y hxy
  apply P10Rose.SubArcMove.bool_eq_of_iff
  rw [roseJunctionCore_lobeColour_eq_true_iff, roseJunctionCore_lobeColour_eq_true_iff]
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ hxy)⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, Relation.EqvGen.trans _ _ _ h
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hxy))⟩

/-- The lobe of one root is the region of that root. -/
theorem roseJunctionCore_lobeColour_singleton (M : CombMap.{v}) (keep : M.Dart → Prop)
    (r : M.Dart) :
    roseJunctionCore_lobeColour M keep [r] = P10Rose.SubArcMove.regionColour M keep r := by
  funext x
  apply P10Rose.SubArcMove.bool_eq_of_iff
  rw [roseJunctionCore_lobeColour_eq_true_iff, P10Rose.SubArcMove.regionColour_eq_true_iff]
  constructor
  · rintro ⟨r', hr', h⟩
    rw [List.mem_singleton] at hr'
    subst hr'
    exact h
  · exact fun h => ⟨r, List.mem_singleton.mpr rfl, h⟩

/-- **A lobe rooted on the cycle stays inside**: no dart of a face outside the face set is
coloured, because a walk class never leaves the face set. -/
theorem roseJunctionCore_lobeColour_eq_false_of_not_mem {M : CombMap.{v}}
    {faces : Finset M.Face} {c : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    {rs : List M.Dart} (hrs : ∀ r ∈ rs, r ∈ c) {x : M.Dart} (hx : M.faceOf x ∉ faces) :
    roseJunctionCore_lobeColour M (walkKeep M c) rs x = false := by
  apply roseJunctionCore_lobeColour_eq_false
  intro r hr hrx
  obtain ⟨hin, -⟩ := (hc r).mp (hrs r hr)
  exact hx ((P10Rose.faceOf_mem_iff_of_walkEqvGen hc hrx).mp hin)

/-- A lobe rooted on the cycle never colours the outer side of a cycle dart. -/
theorem roseJunctionCore_lobeColour_alpha_eq_false {M : CombMap.{v}}
    {faces : Finset M.Face} {c : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    {rs : List M.Dart} (hrs : ∀ r ∈ rs, r ∈ c) {d : M.Dart} (hd : d ∈ c) :
    roseJunctionCore_lobeColour M (walkKeep M c) rs (M.alpha d) = false := by
  obtain ⟨-, hout⟩ := (hc d).mp hd
  exact roseJunctionCore_lobeColour_eq_false_of_not_mem hc hrs hout

/-- Removing a lobe rooted on the cycle keeps every outside face (the exterior, the source)
outside. -/
theorem roseJunctionCore_not_mem_flipFaces {M : CombMap.{v}}
    {faces : Finset M.Face} {c : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    {rs : List M.Dart} (hrs : ∀ r ∈ rs, r ∈ c) {f : M.Face} (hf : f ∉ faces) :
    f ∉ flipFaces M faces (roseJunctionCore_lobeColour M (walkKeep M c) rs) :=
  not_mem_flipFaces (roseJunctionCore_lobeColour_step M (walkKeep M c) rs) hf
    (fun x hx => roseJunctionCore_lobeColour_eq_false_of_not_mem hc hrs (by rw [hx]; exact hf))

/-- An inside face with an uncoloured dart stays inside (the kept cell). -/
theorem roseJunctionCore_mem_flipFaces {M : CombMap.{v}} {faces : Finset M.Face}
    {c : List M.Dart} (rs : List M.Dart) {x : M.Dart} (hx : M.faceOf x ∈ faces)
    (hzx : roseJunctionCore_lobeColour M (walkKeep M c) rs x = false) :
    M.faceOf x ∈ flipFaces M faces (roseJunctionCore_lobeColour M (walkKeep M c) rs) :=
  (mem_flipFaces_iff (roseJunctionCore_lobeColour_step M (walkKeep M c) rs) x).mpr
    ⟨fun _ => hzx, fun _ => hx⟩

/-- Every root is removed by the move. -/
theorem roseJunctionCore_movePred_root (M : CombMap.{v}) (keep : M.Dart → Prop)
    {rs : List M.Dart} {r : M.Dart} (hr : r ∈ rs) :
    movePred M (roseJunctionCore_lobeColour M keep rs) r = false := by
  have h : roseJunctionCore_lobeColour M keep rs r = true :=
    (roseJunctionCore_lobeColour_eq_true_iff M keep rs r).mpr ⟨r, hr, Relation.EqvGen.refl r⟩
  simp [movePred, h]

/-- **Removal of an inside lobe, or one extremal region** (OPEN, PLAUSIBLE; the corrected
planarity core of the rose step).  Under the rose hypotheses there are roots `rs`, either a
nonempty list of cycle darts (remove the union of their walk classes, all inside the face set) or
one dart `r` whose region avoids the exterior and meets a side of a cycle dart, such that with
`z = lobeColour rs` the kept darts are listed as a closed dart walk `s₁ ++ t₁⁻¹ ++ s₂ ++ t₂` with
the clauses of `RoseRegionMoveSubArcStatement`.  See the module docstring for the evidence. -/
def roseJunctionCore_LobeRemovalStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ rs : List X.toCombMap.Dart,
          ((rs ≠ [] ∧ ∀ r ∈ rs, r ∈ K.boundary.cycle) ∨
            ∃ r, rs = [r] ∧
              (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
                (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
              ∃ y ∈ K.boundary.cycle, Relation.EqvGen
                (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r y ∨
                Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
                  (walkKeep X.toCombMap K.boundary.cycle)) r (X.toCombMap.alpha y)) ∧
          ∃ (source kept : Fin X.rCellCount),
            (cell X source).face ∉ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
              X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs) ∧
            (cell X kept).face ∈ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
              X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs) ∧
            ∃ (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
              (s₁ s₂ : List X.toCombMap.Dart),
              List.Perm (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
                (K.boundary.cycle.filter (movePred X.toCombMap (roseJunctionCore_lobeColour
                  X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs))) ∧
              IsClosedDartWalk X.toCombMap (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts) ∧
              s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
              t₂.start.1 + t₂.length ≤ hi ∧
              t₁.length < (cellDarts X source).length ∧ t₂.length < (outerDarts X).length

/-- **The sub-arc region move from the removal of a lobe**: flip the lobe.  For roots on the cycle
the region clauses hold by the lobe API; for one extremal region as in
`regionMoveSubArc_of_singleRegionMove`. -/
theorem roseJunctionCore_regionMoveSubArc_of_lobeRemoval
    (h : roseJunctionCore_LobeRemovalStatement.{u, w, v}) :
    P10Rose.RoseRegionMoveSubArcStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨rs, hcase, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, hwalk,
    hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩ := h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  have hc := K.boundary.cycle_mem_iff
  rcases hcase with ⟨hne, hrs⟩ | ⟨r, rfl, hrout, y, hy, hry⟩
  · obtain ⟨r, hr⟩ : ∃ r, r ∈ rs := by
      cases rs with
      | nil => exact absurd rfl hne
      | cons a l => exact ⟨a, by simp⟩
    exact ⟨roseJunctionCore_lobeColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs,
      roseJunctionCore_lobeColour_step X.toCombMap _ rs,
      fun d hd => Or.inr (roseJunctionCore_lobeColour_alpha_eq_false hc hrs hd),
      roseJunctionCore_not_mem_flipFaces hc hrs K.outerFace_not_mem,
      ⟨r, hrs r hr, roseJunctionCore_movePred_root X.toCombMap _ hr⟩, source, kept, hsource,
      hkept, t₁, t₂, s₁, s₂, hperm, hwalk, hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩
  · rw [roseJunctionCore_lobeColour_singleton] at hsource hkept hperm
    have hz := P10Rose.SubArcMove.regionColour_step X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) r
    exact ⟨P10Rose.SubArcMove.regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r,
      hz, P10Rose.SubArcMove.regionColour_indep hc r,
      not_mem_flipFaces hz K.outerFace_not_mem
        (fun x hx => P10Rose.SubArcMove.regionColour_eq_false X.toCombMap _ (hrout x hx)),
      ⟨y, hy, P10Rose.SubArcMove.movePred_regionColour_eq_false hry⟩, source, kept, hsource,
      hkept, t₁, t₂, s₁, s₂, hperm, hwalk, hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩

/-- **The removal of a lobe from a single-region move** (truth certificate: the residual is
implied by the old target; take the one root `r`). -/
theorem roseJunctionCore_lobeRemoval_of_singleRegionMove
    (h : P10Rose.RoseSingleRegionMoveStatement.{u, w, v}) :
    roseJunctionCore_LobeRemovalStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hrout, hry, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, hwalk,
    hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩ := h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  rw [← roseJunctionCore_lobeColour_singleton] at hsource hkept hperm
  exact ⟨[r], Or.inr ⟨r, rfl, hrout, hry⟩, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm,
    hwalk, hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩

/-- **The removal of a lobe from the (FALSE) junction witness**: the residual is weaker. -/
theorem roseJunctionCore_lobeRemoval_of_junction (h : RoseExtremalJunctionStatement.{u, w, v}) :
    roseJunctionCore_LobeRemovalStatement.{u, w, v} :=
  roseJunctionCore_lobeRemoval_of_singleRegionMove (singleRegionMove_of_junction h)

/-- **The rose step from the removal of a lobe.** -/
theorem roseJunctionCore_rose_of_lobeRemoval
    (h : roseJunctionCore_LobeRemovalStatement.{u, w, v}) :
    P10ChordLift.RoseStepStatement.{u, w, v} :=
  P10Rose.rose_of_regionMoveSubArc (roseJunctionCore_regionMoveSubArc_of_lobeRemoval h)

/-- **The Greendlinger leaf from the removal of a lobe**: the route of
`AssemblyResidual.relativeGreendlinger_of_residuals` with its FALSE binder `hjunction` replaced by
the lobe-removal residual. -/
theorem roseJunctionCore_relativeGreendlinger_of_lobeRemoval
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (hlobe : roseJunctionCore_LobeRemovalStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  P06Bypass.relativeGreendlingerQuasiGeodesicLeastArea_of_fourResidualsBelow
    Piece01.proof.{u, w, v} Piece04.proof.{u, w, v}
    (P06Bypass.refutedBelowSection_of_innerPocketEnclosed
      (P07InnerPocket.innerPocketEnclosed_of_fourPieceOff hoff))
    (Piece10.proof_of_regionMoveSubArc (roseJunctionCore_regionMoveSubArc_of_lobeRemoval hlobe))

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

universe u w v

/-- **The outer-pinch step from the removal of a lobe.** -/
theorem roseJunctionCore_proof_of_lobeRemoval
    (h : P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  proof_of_regionMoveSubArc
    (P10RoseExtremalTrim.roseJunctionCore_regionMoveSubArc_of_lobeRemoval h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_lobeColour
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_lobeColour_eq_true_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_lobeColour_eq_false
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_lobeColour_step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_lobeColour_singleton
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_lobeColour_eq_false_of_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_lobeColour_alpha_eq_false
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_not_mem_flipFaces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_mem_flipFaces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_movePred_root
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_regionMoveSubArc_of_lobeRemoval
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_lobeRemoval_of_singleRegionMove
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_lobeRemoval_of_junction
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_rose_of_lobeRemoval
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_relativeGreendlinger_of_lobeRemoval
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.roseJunctionCore_proof_of_lobeRemoval
