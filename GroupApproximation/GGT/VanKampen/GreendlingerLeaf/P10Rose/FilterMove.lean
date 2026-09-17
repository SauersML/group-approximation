import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# The rose filter step from a region move

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  This module reduces `RoseFilterStepStatement` (module
`P10Rose/InPlaceFilter`) to a purely combinatorial colouring claim, `RoseRegionMoveStatement`, and
proves the reduction `filterStep_of_regionMove`.  Items 1 to 3 of the plan in the docstring of
`P10Rose/InPlaceFilter` are proved here; item 4, the existence of a good move, is the gap.

## The region move

Let `M` be a combinatorial map, `F` a finite set of faces and `c` a list whose members are exactly
the boundary darts of `F` (a `BoundaryCycle`).  Call the classes of the relation
`FaceClassStep M (walkKeep M c)` (move around a face, or cross an edge off `c`) *regions*.  A
*move* is a dart colouring `z : Dart → Bool` constant on regions (constant along each step); `z = true`
marks the regions to flip.  Put

* `flipFaces M F z = {f | f ∈ F ↔ z = false on f}`, the symmetric difference of `F` with the union
  of the flipped regions (`flipFaces`); membership is read off any dart of `f` because `z` is
  constant along `facePerm` (`mem_flipFaces_iff`, from `eqvGen_faceClass_of_sameCycle`);
* `movePred M z d = !z d && !z (α d)`: neither side of `d` is flipped (`movePred`).

1. *Faces.*  A face on which `z` is `false` keeps its membership in `F` (`not_mem_flipFaces`,
   `mem_flipFaces`).  So the exterior face and the source cell stay out, and the kept cell stays in,
   when `z` vanishes on them.
2. *Boundary* (`isBoundaryDart_flipFaces_iff`).  Suppose that no dart of `c` has both sides flipped.
   Then the boundary darts of `flipFaces M F z` are exactly the darts `d ∈ c` with
   `movePred M z d = true`.
   * If `d ∈ c`, then `face d ∈ F` and `face (α d) ∉ F`; `d` is a boundary dart of the new set iff
     `z d = false` (so `face d` stays in) and `z (α d) = false` (so `face (α d)` stays out).
   * If `α d ∈ c`, then `face d ∉ F` and `face (α d) ∈ F`; `d` would be a boundary dart only if
     both sides of `α d` are flipped, which is excluded.
   * Otherwise `d` and `α d` are joined by a step, so `z d = z (α d)`, and `face d ∈ F ↔
     face (α d) ∈ F` (`faceOf_mem_iff_of_walkEqvGen`); hence both faces are in the new set or both
     are out, and `d` is not a boundary dart.
3. *Arcs.*  A dart of the target arc `t_2` has the exterior face across it, and a dart of the
   reversed source arc `t_1⁻¹` has the source cell across it (`faceOf_alpha_of_mem_targetArc`,
   `faceOf_alpha_of_mem_invSourceArc`).  If `z` vanishes on these darts and on those two faces,
   `movePred` keeps both arcs.
4. *Shared vertex.*  If `c` and `c.filter (movePred M z)` are closed dart walks and some dart of `c`
   is removed, some kept dart shares its vertex with a removed one
   (`FilterWalk.exists_shared_vertex_of_filter`, module `P10Rose/FilterWalk`).

With `F' = flipFaces M F z`, `kept` unchanged and `p = movePred M z`, items 1 to 4 give every clause
of `RoseFilterStepStatement`.

## The remaining claim (`RoseRegionMoveStatement`)

Under the hypotheses of the rose step there is a move `z` that vanishes on the exterior face, the
source cell and the kept cell, never flips both sides of a dart of `c`, does not flip the `F`-side
of an arc dart, keeps `c.filter (movePred z)` a closed dart walk, and removes at least one dart of
`c`.  This is the region-union move `F' = (F \ Fs) ∪ Ns` of `P10Rose/InPlaceFilter`, item 4, stated
as a colouring of darts.  It is supported by the exhaustive search recorded there (every
configuration with at most six walk darts and four visits per vertex has such a move, some needing
several regions flipped at once); the planarity argument for arbitrary length (non-interleaving of
regions around a vertex) is not formalised.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides

namespace FilterMove

/-- **The kept darts of a move**: neither side is flipped. -/
def movePred (M : CombMap.{v}) (z : M.Dart → Bool) (d : M.Dart) : Bool :=
  !z d && !z (M.alpha d)

theorem movePred_eq_true_iff (M : CombMap.{v}) (z : M.Dart → Bool) (d : M.Dart) :
    movePred M z d = true ↔ z d = false ∧ z (M.alpha d) = false := by
  cases hd : z d <;> cases ha : z (M.alpha d) <;> simp [movePred, hd, ha]

/-- **The face set after a move**: the faces whose membership in `faces` agrees with `z = false`. -/
noncomputable def flipFaces (M : CombMap.{v}) (faces : Finset M.Face) (z : M.Dart → Bool) :
    Finset M.Face := by
  classical
  exact Finset.univ.filter fun f => ∃ x, M.faceOf x = f ∧ (M.faceOf x ∈ faces ↔ z x = false)

/-- A Boolean function constant along a relation is constant along its equivalence closure. -/
theorem eq_of_eqvGen {α : Type*} {r : α → α → Prop} {z : α → Bool}
    (hz : ∀ x y, r x y → z x = z y) {x y : α} (h : Relation.EqvGen r x y) : z x = z y := by
  induction h with
  | rel a₁ a₂ hab => exact hz a₁ a₂ hab
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Membership after a move**, read off any dart of the face. -/
theorem mem_flipFaces_iff {M : CombMap.{v}} {faces : Finset M.Face} {keep : M.Dart → Prop}
    {z : M.Dart → Bool} (hz : ∀ x y, CombMap.FaceClassStep M keep x y → z x = z y)
    (x : M.Dart) :
    M.faceOf x ∈ flipFaces M faces z ↔ (M.faceOf x ∈ faces ↔ z x = false) := by
  classical
  unfold flipFaces
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, y, hy, h⟩
    rwa [hy, eq_of_eqvGen hz
      (eqvGen_faceClass_of_sameCycle M keep ((M.faceOf_eq_iff y x).mp hy))] at h
  · intro h
    exact ⟨Finset.mem_univ _, x, rfl, h⟩

/-- An unflipped face outside the face set stays outside. -/
theorem not_mem_flipFaces {M : CombMap.{v}} {faces : Finset M.Face} {keep : M.Dart → Prop}
    {z : M.Dart → Bool} (hz : ∀ x y, CombMap.FaceClassStep M keep x y → z x = z y)
    {f : M.Face} (hf : f ∉ faces) (hzf : ∀ x, M.faceOf x = f → z x = false) :
    f ∉ flipFaces M faces z := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep f
  intro h
  exact hf (((mem_flipFaces_iff hz x).mp h).mpr (hzf x rfl))

/-- An unflipped face inside the face set stays inside. -/
theorem mem_flipFaces {M : CombMap.{v}} {faces : Finset M.Face} {keep : M.Dart → Prop}
    {z : M.Dart → Bool} (hz : ∀ x y, CombMap.FaceClassStep M keep x y → z x = z y)
    {f : M.Face} (hf : f ∈ faces) (hzf : ∀ x, M.faceOf x = f → z x = false) :
    f ∈ flipFaces M faces z := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep f
  exact (mem_flipFaces_iff hz x).mpr ⟨fun _ => hzf x rfl, fun _ => hf⟩

/-- The boundary darts of the moved face set on the old cycle. -/
theorem isBoundaryDart_flipFaces_of_mem {M : CombMap.{v}} {faces : Finset M.Face}
    {c : List M.Dart} {z : M.Dart → Bool}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d) {d : M.Dart}
    (hdc : d ∈ c) :
    ((M.faceOf d ∈ faces ↔ z d = false) ∧ ¬(M.faceOf (M.alpha d) ∈ faces ↔
      z (M.alpha d) = false)) ↔ d ∈ c ∧ z d = false ∧ z (M.alpha d) = false := by
  obtain ⟨hin, hout⟩ := (hc d).mp hdc
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hdc, h1.mp hin, ?_⟩
    by_contra h3
    exact h2 ⟨fun h => absurd h hout, fun h => absurd h h3⟩
  · rintro ⟨-, h1, h2⟩
    exact ⟨⟨fun _ => h1, fun _ => hin⟩, fun h => hout (h.mpr h2)⟩

/-- A dart off the old cycle is not a boundary dart of the moved face set. -/
theorem not_isBoundaryDart_flipFaces_of_not_mem {M : CombMap.{v}} {faces : Finset M.Face}
    {c : List M.Dart} {z : M.Dart → Bool}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y → z x = z y)
    (hind : ∀ d ∈ c, z d = false ∨ z (M.alpha d) = false) {d : M.Dart} (hdc : d ∉ c)
    (h1 : M.faceOf d ∈ faces ↔ z d = false)
    (h2 : ¬(M.faceOf (M.alpha d) ∈ faces ↔ z (M.alpha d) = false)) : False := by
  by_cases hac : M.alpha d ∈ c
  · obtain ⟨hin, hout⟩ := (hc _).mp hac
    rw [M.alpha_involutive d] at hout
    have hzd : z d ≠ false := fun h => hout (h1.mpr h)
    have hza : z (M.alpha d) ≠ false := fun h => h2 ⟨fun _ => h, fun _ => hin⟩
    rcases hind _ hac with h | h
    · exact hza h
    · rw [M.alpha_involutive d] at h
      exact hzd h
  · have hstep : CombMap.FaceClassStep M (walkKeep M c) d (M.alpha d) :=
      Or.inr ⟨fun hk => Or.elim hk hdc hac, rfl⟩
    have hzeq := hz d (M.alpha d) hstep
    have hfeq := faceOf_mem_iff_of_walkEqvGen hc (Relation.EqvGen.rel _ _ hstep)
    rw [← hzeq, ← hfeq] at h2
    exact h2 h1

/-- **The boundary of the moved face set** is the old cycle filtered by `movePred`, when no dart of
the cycle has both sides flipped. -/
theorem isBoundaryDart_flipFaces_iff {M : CombMap.{v}} {faces : Finset M.Face}
    {c : List M.Dart} {z : M.Dart → Bool}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y → z x = z y)
    (hind : ∀ d ∈ c, z d = false ∨ z (M.alpha d) = false) (d : M.Dart) :
    Surgery.MapCollapse.IsBoundaryDart M (flipFaces M faces z) d ↔
      d ∈ c ∧ movePred M z d = true := by
  rw [movePred_eq_true_iff]
  show M.faceOf d ∈ flipFaces M faces z ∧ M.faceOf (M.alpha d) ∉ flipFaces M faces z ↔ _
  rw [mem_flipFaces_iff hz, mem_flipFaces_iff hz]
  by_cases hdc : d ∈ c
  · exact isBoundaryDart_flipFaces_of_mem hc hdc
  · refine ⟨fun h => ?_, fun h => absurd h.1 hdc⟩
    exact (not_isBoundaryDart_flipFaces_of_not_mem hc hz hind hdc h.1 h.2).elim

section Arcs

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- Across a dart of the target arc lies the exterior face. -/
theorem faceOf_alpha_of_mem_targetArc (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.targetArc.darts) :
    X.toCombMap.faceOf (X.toCombMap.alpha d) = X.outerFace := by
  have hmem : d ∈ outerDarts X := K.targetArc.mem_cycle_of_mem_darts hd
  simp only [outerDarts, List.mem_map, List.mem_reverse] at hmem
  obtain ⟨e, he, rfl⟩ := hmem
  rw [X.toCombMap.alpha_involutive e]
  exact ((X.faceBoundary X.outerFace).mem_iff e).mp he

/-- Across a dart of the reversed source arc lies the source cell. -/
theorem faceOf_alpha_of_mem_invSourceArc (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ invDarts X K.sourceArc.darts) :
    X.toCombMap.faceOf (X.toCombMap.alpha d) = (cell X K.source).face := by
  simp only [invDarts, List.mem_map, List.mem_reverse] at hd
  obtain ⟨e, he, rfl⟩ := hd
  rw [X.toCombMap.alpha_involutive e]
  exact ((X.faceBoundary (cell X K.source).face).mem_iff e).mp
    (K.sourceArc.mem_cycle_of_mem_darts he)

end Arcs

end FilterMove

open FilterMove

/-- **A region move for the rose step** (OPEN; the isolated remaining claim of `P10Rose`).  Under
the hypotheses of `RoseFilterStepStatement`, some dart colouring `z`, constant along the face-class
steps of the boundary cycle, vanishes on the exterior face, the source cell, the kept cell and the
darts of both arcs, never flips both sides of a dart of the cycle, and the darts of the cycle with
neither side flipped form, in cycle order, a closed dart walk missing at least one dart.

**FALSE; do not use as a gap.**  The three-petal flower in the docstring of
`RoseFilterStepStatement` forces `z` to vanish on every dart.  The open gap of `P10Rose` is
`RoseInPlaceStepStatement`. -/
def RoseRegionMoveStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ z : X.toCombMap.Dart → Bool,
          (∀ x y, CombMap.FaceClassStep X.toCombMap
            (walkKeep X.toCombMap K.boundary.cycle) x y → z x = z y) ∧
          (∀ x, X.toCombMap.faceOf x = X.outerFace → z x = false) ∧
          (∀ x, X.toCombMap.faceOf x = (cell X K.source).face → z x = false) ∧
          (∀ x, X.toCombMap.faceOf x = (cell X K.kept).face → z x = false) ∧
          (∀ d ∈ K.boundary.cycle, z d = false ∨ z (X.toCombMap.alpha d) = false) ∧
          (∀ d ∈ invDarts X K.sourceArc.darts, z d = false) ∧
          (∀ d ∈ K.targetArc.darts, z d = false) ∧
          IsClosedDartWalk X.toCombMap (K.boundary.cycle.filter (movePred X.toCombMap z)) ∧
          ∃ y ∈ K.boundary.cycle, movePred X.toCombMap z y = false

/-- **The rose filter step from a region move**: flip the marked regions of the face set and
filter the boundary cycle by `movePred`. -/
theorem filterStep_of_regionMove (h : RoseRegionMoveStatement.{u, w, v}) :
    RoseFilterStepStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨z, hz, hzout, hzsrc, hzkept, hind, hzt₁, hzt₂, hwalk, y, hy, hpy⟩ :=
    h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  refine ⟨flipFaces X.toCombMap K.faces z, K.kept, movePred X.toCombMap z,
    not_mem_flipFaces hz K.outerFace_not_mem hzout,
    not_mem_flipFaces hz K.source_not_mem hzsrc, mem_flipFaces hz K.kept_mem hzkept,
    isBoundaryDart_flipFaces_iff K.boundary.cycle_mem_iff hz hind,
    fun d hd => (movePred_eq_true_iff X.toCombMap z d).mpr
      ⟨hzt₁ d hd, hzsrc _ (faceOf_alpha_of_mem_invSourceArc K hd)⟩,
    fun d hd => (movePred_eq_true_iff X.toCombMap z d).mpr
      ⟨hzt₂ d hd, hzout _ (faceOf_alpha_of_mem_targetArc K hd)⟩, hwalk, ?_⟩
  have hw : IsClosedDartWalk X.toCombMap K.boundary.cycle :=
    ⟨K.boundary.cycle_nonempty, hK.1, hK.2⟩
  exact FilterWalk.exists_shared_vertex_of_filter (movePred X.toCombMap z) hw hwalk hy hpy

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.movePred
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.movePred_eq_true_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.flipFaces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.eq_of_eqvGen
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.mem_flipFaces_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.not_mem_flipFaces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.mem_flipFaces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.isBoundaryDart_flipFaces_of_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.not_isBoundaryDart_flipFaces_of_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.isBoundaryDart_flipFaces_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.faceOf_alpha_of_mem_targetArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.faceOf_alpha_of_mem_invSourceArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.RoseRegionMoveStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.filterStep_of_regionMove
