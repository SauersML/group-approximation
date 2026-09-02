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
