import GroupApproximation.Manuscript.NonMF.Full.GL05c.Statement
import GroupApproximation.Meta.AxiomGuard

/-!
# How `ExtremalEndBlockConclusion` fails for one dart

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane nm-gl05c-01.

`ExtremalEndBlockConclusion K r` (module `GL05c/Statement`) has six conjuncts.  This file proves
the four ways one dart `r` can fail it, which are the four ways the 16-dart model of
`GL05c/EndBlockRefutation` fails it:

* `endBlock_not_conclusion_of_outer`: the class of `r` meets the exterior face;
* `endBlock_not_conclusion_of_kept`: the class of `r` contains a dart of the kept cell, so the move
  flips the kept cell out of the face set;
* `endBlock_not_conclusion_of_targetArc`, `endBlock_not_conclusion_of_invSourceArc`: the kept
  darts on `t_2`, respectively on `t_1⁻¹`, do not form an end block;
* `endBlock_forall_not_conclusion`: if every dart fails in one of these four ways, no dart
  satisfies the conclusion.

The three-dart patterns of the model are handled by `endBlock_not_isEndBlock_middle`
(`false, true, false`) and `endBlock_not_isEndBlock_ends` (`true, false, true`).

## Manuscript status

Infrastructure for `thm:hull` (`non_mf_groups_exist.tex`, tex 2121, through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL05c

universe u w v

open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

/-! ## Three-element lists that are not end blocks -/

/-- **A middle block is not an end block**: on `[a, b, c]`, a predicate true only on `b` filters to
`[b]`, which is neither a prefix nor a suffix. -/
theorem endBlock_not_isEndBlock_middle {α : Type*} {p : α → Bool} {a b c : α}
    (hab : b ≠ a) (hbc : b ≠ c) (ha : p a = false) (hb : p b = true) (hc : p c = false) :
    ¬GL05b.IsEndBlock p [a, b, c] := by
  have hf : [a, b, c].filter p = [b] := by simp [ha, hb, hc]
  rintro ⟨i, h | h⟩ <;> rw [hf] at h <;> rcases i with _ | _ | _ | i <;> simp at h <;> simp_all

/-- **Two end darts are not an end block**: on `[a, b, c]`, a predicate false only on `b` filters
to `[a, c]`, which is neither a prefix nor a suffix. -/
theorem endBlock_not_isEndBlock_ends {α : Type*} {p : α → Bool} {a b c : α}
    (hab : a ≠ b) (hcb : c ≠ b) (ha : p a = true) (hb : p b = false) (hc : p c = true) :
    ¬GL05b.IsEndBlock p [a, b, c] := by
  have hf : [a, b, c].filter p = [a, c] := by simp [ha, hb, hc]
  rintro ⟨i, h | h⟩ <;> rw [hf] at h <;> rcases i with _ | _ | _ | i <;> simp at h <;> simp_all

/-! ## The four failures of the conclusion -/

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}
  {D : GGT.RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A class meeting the exterior face fails the conclusion** (its second conjunct). -/
theorem endBlock_not_conclusion_of_outer (K : PocketFaceSet D eps X lo hi)
    {r x : X.toCombMap.Dart} (hx : X.toCombMap.faceOf x = X.outerFace)
    (hr : Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle)) r x) :
    ¬ExtremalEndBlockConclusion K r :=
  fun h => h.2.1 x hx hr

/-- **A class containing a dart of the kept cell flips the kept cell out.**  The class then
contains every dart of the kept cell, so no dart of it keeps its membership. -/
theorem endBlock_kept_not_mem_flipFaces (K : PocketFaceSet D eps X lo hi)
    {r x₀ : X.toCombMap.Dart} (hx₀ : X.toCombMap.faceOf x₀ = (cell X K.kept).face)
    (hr : Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle)) r x₀) :
    (cell X K.kept).face ∉ flipFaces X.toCombMap K.faces
      (GL05b.regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) := by
  refine not_mem_flipFaces fun x hx hiff => ?_
  have hsame : X.toCombMap.facePerm.SameCycle x₀ x :=
    (X.toCombMap.faceOf_eq_iff x₀ x).mp (hx₀.trans hx.symm)
  have hrx : Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle)) r x :=
    Relation.EqvGen.trans _ _ _ hr (eqvGen_faceClass_of_sameCycle _ _ hsame)
  have hin : X.toCombMap.faceOf x ∈ K.faces := by
    rw [hx]
    exact K.kept_mem
  have htrue := (GL05b.regionColour_eq_true_iff _ _ _ _).mpr hrx
  have hfalse := hiff.mp hin
  exact absurd (htrue.symm.trans hfalse) (by decide)

/-- **A class containing a dart of the kept cell fails the conclusion** (its fourth conjunct). -/
theorem endBlock_not_conclusion_of_kept (K : PocketFaceSet D eps X lo hi)
    {r x₀ : X.toCombMap.Dart} (hx₀ : X.toCombMap.faceOf x₀ = (cell X K.kept).face)
    (hr : Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle)) r x₀) :
    ¬ExtremalEndBlockConclusion K r :=
  fun h => endBlock_kept_not_mem_flipFaces K hx₀ hr h.2.2.2.1

/-- **No end block on `t_2` fails the conclusion** (its fifth conjunct). -/
theorem endBlock_not_conclusion_of_targetArc (K : PocketFaceSet D eps X lo hi)
    {r : X.toCombMap.Dart}
    (hne : ¬GL05b.IsEndBlock (GL05b.movePred X.toCombMap
      (GL05b.regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))
      K.targetArc.darts) :
    ¬ExtremalEndBlockConclusion K r :=
  fun h => hne h.2.2.2.2.1

/-- **No end block on `t_1⁻¹` fails the conclusion** (its sixth conjunct). -/
theorem endBlock_not_conclusion_of_invSourceArc (K : PocketFaceSet D eps X lo hi)
    {r : X.toCombMap.Dart}
    (hne : ¬GL05b.IsEndBlock (GL05b.movePred X.toCombMap
      (GL05b.regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))
      (invDarts X K.sourceArc.darts)) :
    ¬ExtremalEndBlockConclusion K r :=
  fun h => hne h.2.2.2.2.2

/-- **The four failures cover every dart**: then no dart satisfies the conclusion. -/
theorem endBlock_forall_not_conclusion (K : PocketFaceSet D eps X lo hi)
    (hcases : ∀ r : X.toCombMap.Dart,
      (∃ x, X.toCombMap.faceOf x = X.outerFace ∧ Relation.EqvGen (CombMap.FaceClassStep
        X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∨
      (∃ x, X.toCombMap.faceOf x = (cell X K.kept).face ∧ Relation.EqvGen (CombMap.FaceClassStep
        X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∨
      ¬GL05b.IsEndBlock (GL05b.movePred X.toCombMap
        (GL05b.regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))
        K.targetArc.darts ∨
      ¬GL05b.IsEndBlock (GL05b.movePred X.toCombMap
        (GL05b.regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))
        (invDarts X K.sourceArc.darts)) :
    ∀ r : X.toCombMap.Dart, ¬ExtremalEndBlockConclusion K r := by
  intro r
  rcases hcases r with ⟨x, hx, hr⟩ | ⟨x, hx, hr⟩ | hne | hne
  · exact endBlock_not_conclusion_of_outer K hx hr
  · exact endBlock_not_conclusion_of_kept K hx hr
  · exact endBlock_not_conclusion_of_targetArc K hne
  · exact endBlock_not_conclusion_of_invSourceArc K hne

end Pocket

end GroupApproximation.Full.GL05c

#audit_axioms GroupApproximation.Full.GL05c.endBlock_not_isEndBlock_middle
#audit_axioms GroupApproximation.Full.GL05c.endBlock_not_isEndBlock_ends
#audit_axioms GroupApproximation.Full.GL05c.endBlock_not_conclusion_of_outer
#audit_axioms GroupApproximation.Full.GL05c.endBlock_kept_not_mem_flipFaces
#audit_axioms GroupApproximation.Full.GL05c.endBlock_not_conclusion_of_kept
#audit_axioms GroupApproximation.Full.GL05c.endBlock_not_conclusion_of_targetArc
#audit_axioms GroupApproximation.Full.GL05c.endBlock_not_conclusion_of_invSourceArc
#audit_axioms GroupApproximation.Full.GL05c.endBlock_forall_not_conclusion
