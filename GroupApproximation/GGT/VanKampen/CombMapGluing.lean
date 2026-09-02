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

/-- The retained dart set has one copy of every inner dart for each seam
copy. -/
theorem copiedInnerDart_card
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (n : ℕ) :
    Nat.card (CopiedInnerDart Delta n) = n * Nat.card (InnerDart Delta) := by
  rw [Nat.card_prod]
  simp only [Nat.card_fin]

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

/-- The finite type of exposed darts in all copies. -/
abbrev ExposedCopiedDart (Delta : DiscDiagram.{u, w, v} W) (n : ℕ) :=
  {d : CopiedInnerDart Delta n // IsExposed Delta d.2}

noncomputable instance exposedCopiedDartFintype
    (Delta : DiscDiagram.{u, w, v} W) (n : ℕ) :
    Fintype (ExposedCopiedDart Delta n) :=
  Fintype.ofFinite _

/-- It is enough to pair the exposed boundary darts.  Internal darts will be
paired by the original edge reversal. -/
structure ExposedPairing (Delta : DiscDiagram.{u, w, v} W) (n : ℕ) where
  /-- Pairing of the copied boundary occurrences. -/
  mate : Perm (ExposedCopiedDart Delta n)
  /-- Boundary pairing reverses twice to the original occurrence. -/
  involutive : Function.Involutive mate
  /-- No oriented boundary occurrence is paired with itself. -/
  fixedPointFree : ∀ d, mate d ≠ d
  /-- Paired boundary occurrences belong to different copies. -/
  changes_copy : ∀ d, (mate d).1.1 ≠ d.1.1

namespace ExposedPairing

variable {Delta : DiscDiagram.{u, w, v} W} {n : ℕ}

/-- Reversing an internal retained dart gives another internal retained dart. -/
theorem reverseInnerDart_not_exposed (d : InnerDart Delta)
    (h : ¬ IsExposed Delta d) :
    ¬ IsExposed Delta (reverseInnerDart Delta d h) := by
  intro hexposed
  apply d.2
  rw [IsExposed, reverseInnerDart, Delta.toCombMap.alpha_involutive] at hexposed
  exact hexposed

/-- Extend an exposed seam pairing by the old reversal on internal edges. -/
noncomputable def alphaFun (B : ExposedPairing Delta n) (d : CopiedInnerDart Delta n) :
    CopiedInnerDart Delta n := by
  classical
  exact if h : IsExposed Delta d.2 then (B.mate ⟨d, h⟩).1
    else (d.1, reverseInnerDart Delta d.2 h)

/-- The extended edge reversal is involutive. -/
theorem alphaFun_involutive (B : ExposedPairing Delta n) :
    Function.Involutive B.alphaFun := by
  classical
  intro d
  by_cases h : IsExposed Delta d.2
  · have hmate : IsExposed Delta (B.mate ⟨d, h⟩).1.2 :=
      (B.mate ⟨d, h⟩).2
    simp [alphaFun, h, hmate]
    exact congrArg Subtype.val (B.involutive ⟨d, h⟩)
  · have hreverse : ¬ IsExposed Delta (reverseInnerDart Delta d.2 h) :=
      reverseInnerDart_not_exposed d.2 h
    simp [alphaFun, h, hreverse]
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact Delta.toCombMap.alpha_involutive d.2.1

/-- The extended edge reversal has no fixed dart. -/
theorem alphaFun_fixedPointFree (B : ExposedPairing Delta n)
    (d : CopiedInnerDart Delta n) : B.alphaFun d ≠ d := by
  classical
  by_cases h : IsExposed Delta d.2
  · simp [alphaFun, h]
    intro hfixed
    apply B.fixedPointFree ⟨d, h⟩
    apply Subtype.ext
    exact hfixed
  · simp [alphaFun, h]
    intro hfixed
    apply Delta.toCombMap.alpha_fixedPointFree d.2.1
    have hsecond := congrArg (fun q ↦ q.2.1) hfixed
    exact hsecond

/-- The extended edge reversal as a permutation. -/
noncomputable def seamAlpha (B : ExposedPairing Delta n) :
    Perm (CopiedInnerDart Delta n) where
  toFun := B.alphaFun
  invFun := B.alphaFun
  left_inv := B.alphaFun_involutive
  right_inv := B.alphaFun_involutive

/-- An exposed pairing canonically gives all seam data. -/
noncomputable def toPairing (B : ExposedPairing Delta n) : Pairing Delta n where
  seamAlpha := B.seamAlpha
  involutive := B.alphaFun_involutive
  fixedPointFree := B.alphaFun_fixedPointFree
  agrees_internal copy d h := by
    classical
    change B.alphaFun (copy, d) = (copy, reverseInnerDart Delta d h)
    simp [alphaFun, h]
  exposed d hd := by
    classical
    change IsExposed Delta (B.alphaFun d).2
    simpa [alphaFun, hd] using (B.mate ⟨d, hd⟩).2
  changes_copy d hd := by
    classical
    change (B.alphaFun d).1 ≠ d.1
    simpa [alphaFun, hd] using B.changes_copy ⟨d, hd⟩

end ExposedPairing

namespace ExposedPairing

variable {Delta : DiscDiagram.{u, w, v} W} {n : ℕ}

/-- Pair exposed boundary occurrences by a fixed-point-free involution on the
copy index.  The indexing equivalence is the landed boundary-order
bookkeeping; no presentation-specific relator data enters this constructor. -/
noncomputable def of_copyMate
    {I : Type v} (index : ExposedCopiedDart Delta n ≃ Fin n × I)
    (index_copy : ∀ d, (index d).1 = d.1.1)
    (copyMate : Perm (Fin n))
    (hinvol : Function.Involutive copyMate)
    (hfree : ∀ i, copyMate i ≠ i) : ExposedPairing Delta n := by
  let mateFun : ExposedCopiedDart Delta n → ExposedCopiedDart Delta n :=
    fun d => index.symm (copyMate (index d).1, (index d).2)
  have hmate_involutive : Function.Involutive mateFun := by
    intro d
    apply index.injective
    simp only [mateFun, Equiv.apply_symm_apply]
    apply Prod.ext
    · exact hinvol (index d).1
    · rfl
  let matePerm : Perm (ExposedCopiedDart Delta n) := {
    toFun := mateFun
    invFun := mateFun
    left_inv := hmate_involutive
    right_inv := hmate_involutive }
  refine {
    mate := matePerm
    involutive := hmate_involutive
    fixedPointFree := ?_
    changes_copy := ?_ }
  · intro d hd
    apply hfree (index d).1
    have h := congrArg index hd
    simpa [matePerm, mateFun, Equiv.apply_symm_apply] using congrArg Prod.fst h
  · intro d hd
    apply hfree (index d).1
    have hmate_index : (index (matePerm d)).1 = copyMate (index d).1 := by
      simp [matePerm, mateFun, Equiv.apply_symm_apply]
    calc
      copyMate (index d).1 = (index (matePerm d)).1 := hmate_index.symm
      _ = (matePerm d).1.1 := index_copy (matePerm d)
      _ = d.1.1 := hd
      _ = (index d).1 := (index_copy d).symm

/-- The boundary-copy swap used by the double of a disc. -/
def doubleCopyMate : Perm (Fin 2) := finRotate 2

/-- The double-copy swap is an involution. -/
theorem doubleCopyMate_involutive : Function.Involutive doubleCopyMate := by
  intro i
  fin_cases i <;> simp [doubleCopyMate, finRotate_apply]

/-- The double-copy swap has no fixed point. -/
theorem doubleCopyMate_fixedPointFree (i : Fin 2) :
    doubleCopyMate i ≠ i := by
  fin_cases i <;> simp [doubleCopyMate, finRotate_apply]

/-- A boundary indexing of the two copies gives the actual exposed mate
permutation for the double, with the two copies paired across every boundary
occurrence. -/
noncomputable def of_doubleCopyMate
    {I : Type v} (index : ExposedCopiedDart Delta 2 ≃ Fin 2 × I)
    (index_copy : ∀ d, (index d).1 = d.1.1) : ExposedPairing Delta 2 :=
  of_copyMate index index_copy doubleCopyMate
    doubleCopyMate_involutive doubleCopyMate_fixedPointFree

end ExposedPairing

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
  by
    change (Surgery.MapCollapse.ofAlphaFacePerm S.seamAlpha
      (copiedFacePerm Delta n) S.involutive S.fixedPointFree).facePerm = _
    exact Surgery.MapCollapse.ofAlphaFacePerm_facePerm S.seamAlpha
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
    (((innerFacePerm Delta) ^ m) d).1 =
      ((Delta.toCombMap.facePerm ^ m) d.1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply]
      change Delta.toCombMap.facePerm
          ((((innerFacePerm Delta) ^ m) d).1) = _
      rw [ih]

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
    exact (innerFacePerm_pow_val m a).trans hm
  have hcopied : (copiedFacePerm Delta n).SameCycle (copy, a) (copy, b) :=
    OrbitClassifier.sameCycle_map (innerFacePerm Delta)
      (copiedFacePerm Delta n) (fun d ↦ (copy, d)) (fun _ ↦ rfl) hinner
  rw [S.closedMap_facePerm]
  exact hcopied

/-- Seam gluing preserves the degree of every copied inner face. -/
theorem faceDegree_eq_source (S : Pairing Delta n)
    (f : S.closedMap.Face) :
    S.closedMap.faceDegree f =
      Delta.toCombMap.faceDegree (S.sourceFace f) := by
  classical
  refine Quotient.inductionOn' f ?_
  intro representative
  let toSource :
      {d : S.closedMap.Dart //
          S.closedMap.faceOf d = S.closedMap.faceOf representative} →
        {d : Delta.toCombMap.Dart //
          Delta.toCombMap.faceOf d =
            Delta.toCombMap.faceOf representative.2.1} :=
    fun d ↦ ⟨d.1.2.1, by
      have h := congrArg S.sourceFace d.2
      simpa only [S.sourceFace_faceOf] using h⟩
  let fromSource :
      {d : Delta.toCombMap.Dart //
          Delta.toCombMap.faceOf d =
            Delta.toCombMap.faceOf representative.2.1} →
        {d : S.closedMap.Dart //
          S.closedMap.faceOf d = S.closedMap.faceOf representative} :=
    fun d ↦ ⟨(representative.1,
      ⟨d.1, by
        rw [d.2]
        exact representative.2.2⟩), by
      apply Quotient.sound
      apply S.sameCycle_of_source_sameCycle
      rw [← Delta.toCombMap.faceOf_eq_iff]
      exact d.2⟩
  let E :
      {d : S.closedMap.Dart //
          S.closedMap.faceOf d = S.closedMap.faceOf representative} ≃
        {d : Delta.toCombMap.Dart //
        Delta.toCombMap.faceOf d =
          Delta.toCombMap.faceOf representative.2.1} := {
    toFun := toSource
    invFun := fromSource
    left_inv := fun d ↦ by
      apply Subtype.ext
      apply Prod.ext
      · have hcopy := congrArg S.sourceCopy d.2
        simpa only [S.sourceCopy_faceOf] using hcopy.symm
      · apply Subtype.ext
        rfl
    right_inv := fun d ↦ by
      apply Subtype.ext
      rfl }
  change Nat.card {d : S.closedMap.Dart //
      S.closedMap.faceOf d = S.closedMap.faceOf representative} =
    Nat.card {d : Delta.toCombMap.Dart //
      Delta.toCombMap.faceOf d =
        Delta.toCombMap.faceOf representative.2.1}
  exact Nat.card_congr E

/-- A seam pairing whose closed map satisfies Euler's planar-sphere
condition. -/
structure Spherical (S : Pairing Delta n) : Prop where
  /-- The seam quotient is connected and has Euler characteristic two. -/
  planar : S.closedMap.IsPlanar

/-- Count data for the quotient of `n` copies.  The first three equations are
the explicit incidence calculation: copied interior cells contribute
`n * (V - 1)` vertices plus the two seam vertices, `n * E` edges, and
`n * (F - 1)` faces.  The equations are the exact hypotheses needed before
the Euler-two conclusion, so no planarity assertion is hidden in the seam
constructor. -/
structure EulerTwoCountData (S : Pairing Delta n) where
  connected : S.closedMap.IsConnected
  vertex_count_eq :
    (S.closedMap.vertexCount : ℤ) =
      (n : ℤ) * (Delta.toCombMap.vertexCount : ℤ) - (n : ℤ) + 2
  edge_count_eq :
    (S.closedMap.edgeCount : ℤ) =
      (n : ℤ) * (Delta.toCombMap.edgeCount : ℤ)
  face_count_eq :
    (S.closedMap.faceCount : ℤ) =
      (n : ℤ) * (Delta.toCombMap.faceCount : ℤ) - (n : ℤ)

/-- The corrected incidence equations for the double of a disc.  `boundary`
is the number of darts on the outer face, so gluing two copies identifies one
boundary cycle in vertices and edges and removes the two outer faces. -/
structure DoubleConnectivityData (S : Pairing Delta 2) where
  /-- A retained boundary dart used as the basepoint of the doubled map. -/
  base : CopiedInnerDart Delta 2
  /-- Every dart in either copy reaches the corresponding base boundary dart. -/
  sameCopy : ∀ (copy : Fin 2) (d : InnerDart Delta),
    Relation.EqvGen S.closedMap.Adjacent (copy, d) (copy, base.2)
  /-- The two base boundary copies are joined across the seam. -/
  crossCopy :
    Relation.EqvGen S.closedMap.Adjacent (0, base.2) (1, base.2)

/-- The explicit same-copy and cross-seam paths imply connectedness of the
doubled map. -/
theorem connected_of_doubleConnectivityData
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {S : Pairing Delta 2}
    (C : DoubleConnectivityData S) :
    S.closedMap.IsConnected := by
  intro d e
  change CopiedInnerDart Delta 2 at d e
  have toZero : ∀ x : CopiedInnerDart Delta 2,
      Relation.EqvGen S.closedMap.Adjacent x (0, C.base.2) := by
    intro x
    rcases x with ⟨copy, d⟩
    have hsame := C.sameCopy copy d
    fin_cases copy
    · simpa using hsame
    · have hcross : Relation.EqvGen S.closedMap.Adjacent
          (1, C.base.2) (0, C.base.2) :=
        Relation.EqvGen.symm _ _ C.crossCopy
      exact Relation.EqvGen.trans _ _ _ hsame hcross
  exact Relation.EqvGen.trans _ _ _ (toZero d)
    (Relation.EqvGen.symm _ _ (toZero e))

/-- The corrected incidence equations for the double of a disc.  `boundary`
is the number of darts on the outer face, so gluing two copies identifies one
boundary cycle in vertices and edges and removes the two outer faces. -/
structure DoubleEulerCountData (S : Pairing Delta 2) where
  connectivity : DoubleConnectivityData S
  boundary : ℕ
  boundary_eq_outerDegree : boundary =
    Delta.toCombMap.faceDegree Delta.outerFace
  vertex_count_eq :
    (S.closedMap.vertexCount : ℤ) + (boundary : ℤ) =
      2 * (Delta.toCombMap.vertexCount : ℤ)
  edge_count_eq :
    (S.closedMap.edgeCount : ℤ) + (boundary : ℤ) =
      2 * (Delta.toCombMap.edgeCount : ℤ)
  face_count_eq :
    (S.closedMap.faceCount : ℤ) + 2 =
      2 * (Delta.toCombMap.faceCount : ℤ)

/-- Removing the outer face from a planar closed-map presentation leaves the
disc Euler equation `V - E + (F - 1) = 1`. -/
theorem disc_interiorEuler_eq_one_of_planar
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (hplanar : Delta.toCombMap.IsPlanar) :
    (Delta.toCombMap.vertexCount : ℤ) -
        (Delta.toCombMap.edgeCount : ℤ) +
        (Delta.toCombMap.faceCount : ℤ) - 1 = 1 := by
  have h := Delta.toCombMap.euler_eq_two hplanar
  linarith

/-- The double incidence equations and source planarity prove the spherical
certificate.  The boundary terms cancel, and the source interior equation is
the preceding `disc_interiorEuler_eq_one_of_planar` identity. -/
theorem spherical_of_doubleEulerCountData
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {S : Pairing Delta 2}
    (C : DoubleEulerCountData S)
    (hplanar : Delta.toCombMap.IsPlanar) :
    Spherical S := by
  refine ⟨connected_of_doubleConnectivityData C.connectivity, ?_⟩
  unfold CombMap.eulerCharacteristic
  have hv := C.vertex_count_eq
  have he := C.edge_count_eq
  have hf := C.face_count_eq
  have hsource := Delta.toCombMap.euler_eq_two hplanar
  linarith

/-- The copied-incidence count gives the Euler-characteristic-two spherical
certificate.  The old disc planarity supplies the identity
`V - E + F = 2`; substituting the three count equations leaves exactly two. -/
theorem spherical_of_eulerTwoCountData
    (S : Pairing Delta n) (C : EulerTwoCountData S)
    (hdisc : Delta.toCombMap.IsPlanar) :
    Spherical S := by
  refine ⟨?_, ?_⟩
  · exact C.connected
  · unfold CombMap.eulerCharacteristic
    rw [C.vertex_count_eq, C.edge_count_eq, C.face_count_eq]
    have hdisc' := Delta.toCombMap.euler_eq_two hdisc
    have hzero :
        (Delta.toCombMap.vertexCount : ℤ) -
            (Delta.toCombMap.edgeCount : ℤ) +
            (Delta.toCombMap.faceCount : ℤ) - 2 = 0 := by
      linarith
    calc
      ((n : ℤ) * (Delta.toCombMap.vertexCount : ℤ) - (n : ℤ) + 2) -
          (n : ℤ) * (Delta.toCombMap.edgeCount : ℤ) +
          ((n : ℤ) * (Delta.toCombMap.faceCount : ℤ) - (n : ℤ)) =
          (n : ℤ) * ((Delta.toCombMap.vertexCount : ℤ) -
            (Delta.toCombMap.edgeCount : ℤ) +
            (Delta.toCombMap.faceCount : ℤ) - 2) + 2 := by ring
      _ = 2 := by rw [hzero]; ring

/-- A boundary mate permutation with the copied incidence equations gives the
spherical seam certificate for a planar source disc.  The mate, connectedness,
and three count equations are the explicit residual inputs; planarity closes
the Euler-two conclusion. -/
theorem ExposedPairing.spherical_of_planarDisc
    (B : ExposedPairing Delta n)
    (C : EulerTwoCountData B.toPairing)
    (hdisc : Delta.toCombMap.IsPlanar) :
    Spherical B.toPairing :=
  Pairing.spherical_of_eulerTwoCountData B.toPairing C hdisc

/-- A spherical seam gives a closed planar combinatorial map. -/
noncomputable def sphericalCombMap (S : Pairing Delta n) (hS : S.Spherical) :
    SphericalCombMap.{v} where
  toCombMap := S.closedMap
  planar := hS.planar

end Pairing

namespace ExposedPairing

variable {Delta : DiscDiagram.{u, w, v} W} {n : ℕ}

/-- The planar-disc spherical certificate is exported at the exposed-pairing
namespace so consumers need not depend on the implementation namespace used
by the Euler-count proof. -/
theorem spherical_of_planarDisc
    (B : ExposedPairing Delta n)
    (C : Pairing.EulerTwoCountData B.toPairing)
    (hdisc : Delta.toCombMap.IsPlanar) :
    Pairing.Spherical B.toPairing :=
  Pairing.ExposedPairing.spherical_of_planarDisc B C hdisc

end ExposedPairing

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

/-- The one-triangle seam bookkeeping has the expected two-copy retained dart
count. -/
theorem copiedInnerDart_two_card_model
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) :
    Nat.card (CopiedInnerDart Delta 2) =
      2 * Nat.card (InnerDart Delta) :=
  copiedInnerDart_card Delta 2

/-- The one-triangle seam bookkeeping has the expected three-copy retained
dart count. -/
theorem copiedInnerDart_three_card_model
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) :
    Nat.card (CopiedInnerDart Delta 3) =
      3 * Nat.card (InnerDart Delta) :=
  copiedInnerDart_card Delta 3

end SeamGluing
end VanKampen
end GGT
end GroupApproximation
