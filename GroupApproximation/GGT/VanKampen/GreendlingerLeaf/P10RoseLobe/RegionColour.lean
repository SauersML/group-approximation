import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.CoreStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# The lobe colouring read as regions of the walk

Lane gl-p10-62.  Notation: `M = X.toCombMap`, `c = K.boundary.cycle`,
`R = EqvGen (FaceClassStep M (walkKeep M c))`; the `R`-classes are the regions of `c`, i.e. the
faces of the planar walk map `Γ = walkMap M c` (`CoreFacts`).  This module translates the Boolean
move calculus of `roseLobeCore_Statement` (`movePred`, `flipFaces`, `lobeColour`) into plain
statements about `R`-classes and positions on `c`:

* `roseLobeRegion_movePred_in`: for roots `rs ⊆ c` (an inside lobe), a dart `d ∈ c` is kept by
  the move iff it lies in no root class;
* `roseLobeRegion_movePred_out`: for the single root `α y` with `y ∈ c` (a lake), a dart `d ∈ c`
  is kept iff `α d` is not in the class of `α y`;
* `roseLobeRegion_block`, `roseLobeRegion_place`: the block and placement clauses of
  `roseLobeCore_Statement`, from their class-form versions `roseLobeRegion_Block`,
  `roseLobeRegion_Place` (any Boolean `P` agreeing on `c` with a Prop `Q`);
* `roseLobeRegion_faceOf_alpha_inv`, `roseLobeRegion_faceOf_alpha_tgt`: the reverse of a dart of
  `I = invDarts X K.sourceArc.darts` lies on the source cell, that of a dart of `K.targetArc`
  on the outer face.

## LOUD: strength

Everything here is PROVED; there is no hypothesis Prop.  The truth check is in `RegionStatement`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

/-- **The block clause in class form**: `c = A ++ B ++ C`, and either `B` is removed and `A ++ C`
is kept (and nonempty), or `B` is kept (and nonempty) and `A ++ C` is removed.  `Q d` reads
"`d` is kept". -/
def roseLobeRegion_Block {α : Type*} (c : List α) (Q : α → Prop) (A B C : List α) : Prop :=
  c = A ++ B ++ C ∧
    (((∀ d ∈ B, ¬Q d) ∧ (∀ d ∈ A ++ C, Q d) ∧ A ++ C ≠ []) ∨
      ((∀ d ∈ B, Q d) ∧ (∀ d ∈ A ++ C, ¬Q d) ∧ B ≠ []))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_Block

/-- **The placement clause in class form** (the no-bubble placement of `roseLobeNoBub_Statement`
relative to the source part `I` and the target part `T` of the walk). -/
def roseLobeRegion_Place {α : Type*} (Q : α → Prop) (I T A B C : List α) : Prop :=
  ((∀ d ∈ A ++ C, ¬Q d) ∨ (∃ d ∈ B, d ∉ I) ∨ B <+: I ∨ B <:+ I) ∧
    ((∀ d ∈ B, d ∉ T) ∨ (C = [] ∧ ∀ d ∈ B, ¬Q d) ∨ ((∀ d ∈ A ++ C, ¬Q d) ∧ ∀ d ∈ A, d ∉ T))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_Place

section Lists

variable {α : Type*} {c : List α} {P : α → Bool} {Q : α → Prop}

theorem roseLobeRegion_mem_B {A B C : List α} (h : c = A ++ B ++ C) {d : α} (hd : d ∈ B) :
    d ∈ c := by
  rw [h]
  exact List.mem_append_left C (List.mem_append_right A hd)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_mem_B

theorem roseLobeRegion_mem_AC {A B C : List α} (h : c = A ++ B ++ C) {d : α} (hd : d ∈ A ++ C) :
    d ∈ c := by
  rw [h]
  rcases List.mem_append.mp hd with hd | hd
  · exact List.mem_append_left C (List.mem_append_left B hd)
  · exact List.mem_append_right (A ++ B) hd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_mem_AC

/-- A sublist of `c` on which `Q` fails everywhere is filtered away by `P`. -/
theorem roseLobeRegion_filter_nil (hPQ : ∀ d ∈ c, P d = true ↔ Q d) {L : List α}
    (hL : ∀ d ∈ L, d ∈ c) (h : ∀ d ∈ L, ¬Q d) : L.filter P = [] :=
  List.filter_eq_nil_iff.mpr fun d hd hp => h d hd ((hPQ d (hL d hd)).mp hp)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_filter_nil

/-- A sublist of `c` on which `Q` holds everywhere is kept by `P`. -/
theorem roseLobeRegion_filter_self (hPQ : ∀ d ∈ c, P d = true ↔ Q d) {L : List α}
    (hL : ∀ d ∈ L, d ∈ c) (h : ∀ d ∈ L, Q d) : L.filter P = L :=
  List.filter_eq_self.mpr fun d hd => (hPQ d (hL d hd)).mpr (h d hd)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_filter_self

/-- **The block clause from its class form.** -/
theorem roseLobeRegion_block (hPQ : ∀ d ∈ c, P d = true ↔ Q d) {A B C : List α}
    (hb : roseLobeRegion_Block c Q A B C) :
    c = A ++ B ++ C ∧
      ((B.filter P = [] ∧ (A ++ C).filter P = A ++ C ∧ A ++ C ≠ []) ∨
        (B.filter P = B ∧ (A ++ C).filter P = [] ∧ B ≠ [])) := by
  obtain ⟨hABC, hb⟩ := hb
  have hB : ∀ d ∈ B, d ∈ c := fun d hd => roseLobeRegion_mem_B hABC hd
  have hAC : ∀ d ∈ A ++ C, d ∈ c := fun d hd => roseLobeRegion_mem_AC hABC hd
  refine ⟨hABC, ?_⟩
  rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨roseLobeRegion_filter_nil hPQ hB h1, roseLobeRegion_filter_self hPQ hAC h2, h3⟩
  · exact Or.inr ⟨roseLobeRegion_filter_self hPQ hB h1, roseLobeRegion_filter_nil hPQ hAC h2, h3⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_block

/-- **The placement clause from its class form.** -/
theorem roseLobeRegion_place (hPQ : ∀ d ∈ c, P d = true ↔ Q d) {I T A B C : List α}
    (hABC : c = A ++ B ++ C) (hp : roseLobeRegion_Place Q I T A B C) :
    (((A ++ C).filter P = [] ∨ (∃ d ∈ B, d ∉ I) ∨ B <+: I ∨ B <:+ I) ∧
      ((∀ d ∈ B, d ∉ T) ∨ (C = [] ∧ B.filter P = []) ∨
        ((A ++ C).filter P = [] ∧ ∀ d ∈ A, d ∉ T))) := by
  obtain ⟨h1, h2⟩ := hp
  have hB : ∀ d ∈ B, d ∈ c := fun d hd => roseLobeRegion_mem_B hABC hd
  have hAC : ∀ d ∈ A ++ C, d ∈ c := fun d hd => roseLobeRegion_mem_AC hABC hd
  refine ⟨?_, ?_⟩
  · rcases h1 with h1 | h1
    · exact Or.inl (roseLobeRegion_filter_nil hPQ hAC h1)
    · exact Or.inr h1
  · rcases h2 with h2 | ⟨h2, h3⟩ | ⟨h2, h3⟩
    · exact Or.inl h2
    · exact Or.inr (Or.inl ⟨h2, roseLobeRegion_filter_nil hPQ hB h3⟩)
    · exact Or.inr (Or.inr ⟨roseLobeRegion_filter_nil hPQ hAC h2, h3⟩)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_place

end Lists

section Colour

variable {M : CombMap.{v}} {faces : Finset M.Face} {c : List M.Dart}

/-- **The move of an inside lobe on the walk**: with roots on `c`, a dart of `c` is kept iff it
lies in no root class. -/
theorem roseLobeRegion_movePred_in
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    {rs : List M.Dart} (hrs : ∀ r ∈ rs, r ∈ c) {d : M.Dart} (hd : d ∈ c) :
    movePred M (roseJunctionCore_lobeColour M (walkKeep M c) rs) d = true ↔
      ∀ r ∈ rs, ¬Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) r d := by
  rw [movePred_eq_true_iff]
  constructor
  · rintro ⟨h, -⟩ r hr hrd
    have h' := (roseJunctionCore_lobeColour_eq_true_iff M (walkKeep M c) rs d).mpr ⟨r, hr, hrd⟩
    rw [h] at h'
    exact Bool.false_ne_true h'
  · intro h
    exact ⟨roseJunctionCore_lobeColour_eq_false M (walkKeep M c) h,
      roseJunctionCore_lobeColour_alpha_eq_false hc hrs hd⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_movePred_in

/-- The region across a walk dart contains no dart of the walk. -/
theorem roseLobeRegion_not_rel_out
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    {y d : M.Dart} (hy : y ∈ c) (hd : d ∈ c) :
    ¬Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) (M.alpha y) d := fun h =>
  ((hc y).mp hy).2 ((P10Rose.faceOf_mem_iff_of_walkEqvGen hc h).mpr ((hc d).mp hd).1)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_not_rel_out

/-- **The move of a lake on the walk**: with the single root `α y`, `y ∈ c`, a dart `d` of `c`
is kept iff `α d` is not in the region of `α y`. -/
theorem roseLobeRegion_movePred_out
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    {y : M.Dart} (hy : y ∈ c) {d : M.Dart} (hd : d ∈ c) :
    movePred M (roseJunctionCore_lobeColour M (walkKeep M c) [M.alpha y]) d = true ↔
      ¬Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) (M.alpha y) (M.alpha d) := by
  have h0 : roseJunctionCore_lobeColour M (walkKeep M c) [M.alpha y] d = false := by
    apply roseJunctionCore_lobeColour_eq_false
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact roseLobeRegion_not_rel_out hc hy hd
  rw [movePred_eq_true_iff, h0]
  constructor
  · rintro ⟨-, h⟩ hyd
    have h' := (roseJunctionCore_lobeColour_eq_true_iff M (walkKeep M c) [M.alpha y]
      (M.alpha d)).mpr ⟨M.alpha y, List.mem_singleton.mpr rfl, hyd⟩
    rw [h] at h'
    exact Bool.false_ne_true h'
  · intro h
    refine ⟨rfl, roseJunctionCore_lobeColour_eq_false M (walkKeep M c) ?_⟩
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_movePred_out

end Colour

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The source part faces the source cell**: the reverse of a dart of
`I = invDarts X K.sourceArc.darts` lies on the source cell. -/
theorem roseLobeRegion_faceOf_alpha_inv (K : PocketFaceSet D eps X lo hi) {d : X.toCombMap.Dart}
    (hd : d ∈ invDarts X K.sourceArc.darts) :
    X.toCombMap.faceOf (X.toCombMap.alpha d) = (cell X K.source).face := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  rw [X.toCombMap.alpha_involutive e]
  exact ((X.faceBoundary (cell X K.source).face).mem_iff e).mp
    (K.sourceArc.mem_cycle_of_mem_darts (List.mem_reverse.mp he))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_faceOf_alpha_inv

/-- **The target part faces the exterior**: the reverse of a dart of `K.targetArc` lies on the
outer face. -/
theorem roseLobeRegion_faceOf_alpha_tgt (K : PocketFaceSet D eps X lo hi) {d : X.toCombMap.Dart}
    (hd : d ∈ K.targetArc.darts) :
    X.toCombMap.faceOf (X.toCombMap.alpha d) = X.outerFace := by
  have hmem : d ∈ outerDarts X := K.targetArc.mem_cycle_of_mem_darts hd
  simp only [outerDarts, List.mem_map, List.mem_reverse] at hmem
  obtain ⟨q, hq, rfl⟩ := hmem
  rw [X.toCombMap.alpha_involutive]
  exact ((X.faceBoundary X.outerFace).mem_iff q).mp hq

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeRegion_faceOf_alpha_tgt

end Pocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
