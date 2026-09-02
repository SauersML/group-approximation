import GroupApproximation.GGT.VanKampen.CombMapStars
import GroupApproximation.GGT.VanKampen.SurgeryMap

/-!
# Reclosing copied disc interiors along boundary seams

This module gives the permutation-map construction used in the power-disc
gluing argument.  The old outer-face darts are removed from each copy.  The
face permutation on every retained inner-face dart is unchanged, while a
supplied fixed-point-free involution pairs retained boundary darts across the
seams.  `closedMap` is then forced by these two permutations.

The source-copy and source-face projections are proved from the unchanged
face permutation.  Thus later relator labels and face degrees can be
transported independently of the vertex calculation at the seams.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace SeamGluing

open Equiv

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}

/-- Darts based in an inner face of a disc diagram.  Removing the darts based
in the distinguished outer face deletes that face before seam gluing. -/
abbrev InnerDart (Delta : DiscDiagram.{u, w, v} W) :=
  {d : Delta.toCombMap.Dart //
    Delta.toCombMap.faceOf d ≠ Delta.outerFace}

noncomputable instance innerDartFintype
    (Delta : DiscDiagram.{u, w, v} W) : Fintype (InnerDart Delta) :=
  Fintype.ofFinite _

/-- Retained darts in `n` labelled copies of the disc interior. -/
abbrev CopiedInnerDart (Delta : DiscDiagram.{u, w, v} W) (n : ℕ) :=
  Fin n × InnerDart Delta

/-- The old face rotation restricts to the darts of inner faces. -/
def innerFacePerm (Delta : DiscDiagram.{u, w, v} W) :
    Perm (InnerDart Delta) where
  toFun d := ⟨Delta.toCombMap.facePerm d.1, by
    rw [Delta.toCombMap.faceOf_facePerm]
    exact d.2⟩
  invFun d := ⟨Delta.toCombMap.facePerm.symm d.1, by
    have hface : Delta.toCombMap.faceOf
        (Delta.toCombMap.facePerm.symm d.1) =
        Delta.toCombMap.faceOf d.1 := by
      have h := Delta.toCombMap.faceOf_facePerm
        (Delta.toCombMap.facePerm.symm d.1)
      simpa only [Delta.toCombMap.facePerm.apply_symm_apply] using h.symm
    rw [hface]
    exact d.2⟩
  left_inv d := by
    apply Subtype.ext
    exact Delta.toCombMap.facePerm.symm_apply_apply d.1
  right_inv d := by
    apply Subtype.ext
    exact Delta.toCombMap.facePerm.apply_symm_apply d.1

/-- Face rotation in copied interiors preserves the copy number. -/
def copiedFacePerm (Delta : DiscDiagram.{u, w, v} W) (n : ℕ) :
    Perm (CopiedInnerDart Delta n) :=
  Equiv.prodCongr (Equiv.refl (Fin n)) (innerFacePerm Delta)

/-- A retained inner dart lies on the old boundary when its reverse was based
in the deleted outer face. -/
def IsExposed (Delta : DiscDiagram.{u, w, v} W)
    (d : InnerDart Delta) : Prop :=
  Delta.toCombMap.faceOf (Delta.toCombMap.alpha d.1) = Delta.outerFace

/-- An unexposed inner dart has a retained old reverse. -/
def reverseInnerDart (Delta : DiscDiagram.{u, w, v} W)
    (d : InnerDart Delta) (h : ¬ IsExposed Delta d) : InnerDart Delta :=
  ⟨Delta.toCombMap.alpha d.1, h⟩

/-- Seam data for copied disc interiors.  Internal edges keep their old
reverse inside a copy; exposed darts are paired with exposed darts in a
different copy. -/
structure Pairing (Delta : DiscDiagram.{u, w, v} W) (n : ℕ) where
  /-- Edge reversal after the boundary copies are identified. -/
  seamAlpha : Perm (CopiedInnerDart Delta n)
  /-- A seam edge still has two oriented sides. -/
  involutive : Function.Involutive seamAlpha
  /-- No seam dart is paired with itself. -/
  fixedPointFree : ∀ d, seamAlpha d ≠ d
  /-- Edges away from the boundary retain the original reversal. -/
  agrees_internal : ∀ (copy : Fin n) (d : InnerDart Delta)
      (h : ¬ IsExposed Delta d),
    seamAlpha (copy, d) = (copy, reverseInnerDart Delta d h)
  /-- A boundary seam is paired only with another boundary seam. -/
  exposed : ∀ d, IsExposed Delta d.2 →
    IsExposed Delta (seamAlpha d).2
  /-- An exposed dart is glued to a different rotated copy. -/
  changes_copy : ∀ d, IsExposed Delta d.2 →
    (seamAlpha d).1 ≠ d.1

namespace Pairing

variable {Delta : DiscDiagram.{u, w, v} W} {n : ℕ}

/-- The closed map obtained by retaining all inner face rotations and
installing the seam edge involution. -/
noncomputable def closedMap (S : Pairing Delta n) : CombMap.{v} :=
  Surgery.MapCollapse.ofAlphaFacePerm S.seamAlpha
    (copiedFacePerm Delta n) S.involutive S.fixedPointFree

/-- The glued map has exactly the copied inner-face permutation. -/
theorem closedMap_facePerm (S : Pairing Delta n) :
    S.closedMap.facePerm = copiedFacePerm Delta n :=
  Surgery.MapCollapse.ofAlphaFacePerm_facePerm S.seamAlpha
    (copiedFacePerm Delta n) S.involutive S.fixedPointFree

/-- Copy number attached to a retained dart. -/
def dartCopy (d : CopiedInnerDart Delta n) : Fin n := d.1

/-- Source inner face attached to a retained dart. -/
def dartSourceFace (d : CopiedInnerDart Delta n) : Delta.toCombMap.Face :=
  Delta.toCombMap.faceOf d.2.1

/-- Face rotation in the glued map preserves the source copy. -/
theorem dartCopy_facePerm (S : Pairing Delta n)
    (d : S.closedMap.Dart) :
    dartCopy (S.closedMap.facePerm d) = dartCopy d := by
  rw [S.closedMap_facePerm]
  rfl

/-- Face rotation in the glued map preserves the source inner face. -/
theorem dartSourceFace_facePerm (S : Pairing Delta n)
    (d : S.closedMap.Dart) :
    dartSourceFace (S.closedMap.facePerm d) = dartSourceFace d := by
  rw [S.closedMap_facePerm]
  exact Delta.toCombMap.faceOf_facePerm d.2.1

/-- Every glued face has a canonical source copy. -/
noncomputable def sourceCopy (S : Pairing Delta n) :
    S.closedMap.Face → Fin n :=
  Quotient.lift dartCopy fun _ _ h ↦
    OrbitClassifier.eq_of_sameCycle S.closedMap.facePerm dartCopy
      S.dartCopy_facePerm h

/-- Every glued face has a canonical source inner face. -/
noncomputable def sourceFace (S : Pairing Delta n) :
    S.closedMap.Face → Delta.toCombMap.Face :=
  Quotient.lift dartSourceFace fun _ _ h ↦
    OrbitClassifier.eq_of_sameCycle S.closedMap.facePerm dartSourceFace
      S.dartSourceFace_facePerm h

/-- The source of a glued face is never the deleted outer face. -/
theorem sourceFace_ne_outer (S : Pairing Delta n)
    (f : S.closedMap.Face) : S.sourceFace f ≠ Delta.outerFace := by
  refine Quotient.inductionOn' f ?_
  intro d
  exact d.2.2

/-- The source copy of a face represented by `d` is the copy of `d`. -/
theorem sourceCopy_faceOf (S : Pairing Delta n)
    (d : S.closedMap.Dart) :
    S.sourceCopy (S.closedMap.faceOf d) = d.1 :=
  rfl

/-- The source face of a face represented by `d` is the old face of `d`. -/
theorem sourceFace_faceOf (S : Pairing Delta n)
    (d : S.closedMap.Dart) :
    S.sourceFace (S.closedMap.faceOf d) =
      Delta.toCombMap.faceOf d.2.1 :=
  rfl

/-- Restricting the old face permutation does not change its iterates on
underlying darts. -/
theorem innerFacePerm_pow_val (m : ℕ) (d : InnerDart Delta) :
    ((innerFacePerm Delta) ^ m d).1 =
      (Delta.toCombMap.facePerm ^ m) d.1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply]
      change ((innerFacePerm Delta) ^ m (innerFacePerm Delta d)).1 = _
      rw [ih]
      rfl

/-- Two darts in one old inner-face orbit remain in the same copied face
orbit. -/
theorem sameCycle_of_source_sameCycle (S : Pairing Delta n)
    (copy : Fin n) (a b : InnerDart Delta)
    (h : Delta.toCombMap.facePerm.SameCycle a.1 b.1) :
    S.closedMap.facePerm.SameCycle (copy, a) (copy, b) := by
  have hinner : (innerFacePerm Delta).SameCycle a b := by
    obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
    refine ⟨m, ?_⟩
    apply Subtype.ext
    rw [innerFacePerm_pow_val]
    exact hm
  have hcopied : (copiedFacePerm Delta n).SameCycle (copy, a) (copy, b) :=
    OrbitClassifier.sameCycle_map (innerFacePerm Delta)
      (copiedFacePerm Delta n) (fun d ↦ (copy, d)) (fun _ ↦ rfl) hinner
  rw [S.closedMap_facePerm]
  exact hcopied

/-- The dart orbit of a glued face is equivalent to the dart orbit of its
source inner face. -/
noncomputable def faceDartEquiv (S : Pairing Delta n)
    (f : S.closedMap.Face) :
    {d : S.closedMap.Dart // S.closedMap.faceOf d = f} ≃
      {d : Delta.toCombMap.Dart //
        Delta.toCombMap.faceOf d = S.sourceFace f} := by
  refine Quotient.inductionOn' f ?_
  intro representative
  let toSource :
      {d : S.closedMap.Dart //
          S.closedMap.faceOf d = S.closedMap.faceOf representative} →
        {d : Delta.toCombMap.Dart //
          Delta.toCombMap.faceOf d =
            S.sourceFace (S.closedMap.faceOf representative)} :=
    fun d ↦ ⟨d.1.2.1, by
      have h := congrArg S.sourceFace d.2
      simpa only [S.sourceFace_faceOf] using h⟩
  let fromSource :
      {d : Delta.toCombMap.Dart //
          Delta.toCombMap.faceOf d =
            S.sourceFace (S.closedMap.faceOf representative)} →
        {d : S.closedMap.Dart //
          S.closedMap.faceOf d = S.closedMap.faceOf representative} :=
    fun d ↦ ⟨(representative.1,
      ⟨d.1, by
        rw [d.2, S.sourceFace_faceOf]
        exact representative.2.2⟩), by
      apply Quotient.sound
      apply S.sameCycle_of_source_sameCycle
      rw [← Delta.toCombMap.faceOf_eq_iff]
      simpa only [S.sourceFace_faceOf] using d.2.symm⟩
  exact {
    toFun := toSource
    invFun := fromSource
    left_inv := fun d ↦ by
      apply Subtype.ext
      apply Prod.ext
      · have hcopy := congrArg S.sourceCopy d.2
        simpa only [S.sourceCopy_faceOf] using hcopy
      · apply Subtype.ext
        rfl
    right_inv := fun d ↦ by
      apply Subtype.ext
      rfl }

/-- Seam gluing preserves the degree of every copied inner face. -/
theorem faceDegree_eq_source (S : Pairing Delta n)
    (f : S.closedMap.Face) :
    S.closedMap.faceDegree f =
      Delta.toCombMap.faceDegree (S.sourceFace f) := by
  exact Nat.card_congr (S.faceDartEquiv f)

/-- A seam pairing whose closed map satisfies Euler's planar-sphere
condition. -/
structure Spherical (S : Pairing Delta n) : Prop where
  /-- The seam quotient is connected and has Euler characteristic two. -/
  planar : S.closedMap.IsPlanar

/-- A spherical seam gives a closed planar combinatorial map. -/
noncomputable def sphericalCombMap (S : Pairing Delta n) (hS : S.Spherical) :
    SphericalCombMap.{v} where
  toCombMap := S.closedMap
  planar := hS.planar

end Pairing

/-! ## Constructor and one-triangle checks -/

/-- Rebuilding any map from its edge and face permutations is the identity on
face rotation.  This is the local model for the seam constructor before the
global connectedness and Euler count are imposed. -/
def rebuild (M : CombMap.{v}) : CombMap.{v} :=
  Surgery.MapCollapse.ofAlphaFacePerm M.alpha M.facePerm
    M.alpha_involutive M.alpha_fixedPointFree

/-- Rebuilding preserves the complete face rotation. -/
theorem rebuild_facePerm (M : CombMap.{v}) :
    (rebuild M).facePerm = M.facePerm :=
  Surgery.MapCollapse.ofAlphaFacePerm_facePerm M.alpha M.facePerm
    M.alpha_involutive M.alpha_fixedPointFree

/-- On the one-triangle map the rebuilt positive face still advances by one
literal triangle position. -/
theorem oneTriangle_rebuild_facePerm_false (i : ZMod 3) :
    (rebuild oneTriangleCombMap).facePerm (i, false) = (i + 1, false) := by
  rw [rebuild_facePerm]
  exact oneTriangle_facePerm_false i

/-- On the one-triangle map the rebuilt exterior face still advances in the
reverse orientation. -/
theorem oneTriangle_rebuild_facePerm_true (i : ZMod 3) :
    (rebuild oneTriangleCombMap).facePerm (i, true) = (i - 1, true) := by
  rw [rebuild_facePerm]
  exact oneTriangle_facePerm_true i

end SeamGluing
end VanKampen
end GGT
end GroupApproximation
