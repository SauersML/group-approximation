import GroupApproximation.Analysis.NonUnitalMFSupportCorner
import GroupApproximation.Meta.AxiomGuard

/-!
# Unitalizing a nonunital norm-matrix-corona embedding

An injective nonunital star homomorphism from a unital C-star algebra has a
nonzero support projection.  After lifting that projection, retaining every
nonzero coordinate, and compressing to its finite-dimensional ranges, the
represented algebra embeds unitally in the resulting norm-matrix corona.
-/

namespace GroupApproximation
namespace NonUnitalMFSupportCornerEmbedding

open Filter Matrix
open KazhdanCornerMatrices
open NonUnitalMFSupportCorner
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]
variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]

/-! ## Algebra of corner classes -/

theorem cornerClass_zero
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) :
    cornerClass Y P hP hne 0 = 0 := by
  rw [cornerClass, cornerCompressSequence_zero, map_zero]

theorem cornerClass_add
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x y : BoundedMatrixSequence (fun n ↦ Y n)) :
    cornerClass Y P hP hne (x + y) =
      cornerClass Y P hP hne x + cornerClass Y P hP hne y := by
  let q := normMatrixCStarCoronaQuotient
    (fun k ↦ (relabelledCornerModel Y P hP hne k : Type))
  change q (cornerCompressSequence Y P hP hne (x + y)) =
    q (cornerCompressSequence Y P hP hne x) +
      q (cornerCompressSequence Y P hP hne y)
  rw [show cornerCompressSequence Y P hP hne (x + y) =
      cornerCompressSequence Y P hP hne x +
        cornerCompressSequence Y P hP hne y from
    (cornerCompressSequenceLinear Y P hP hne).map_add x y]
  exact q.map_add _ _

theorem cornerClass_smul
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (c : ℂ) (x : BoundedMatrixSequence (fun n ↦ Y n)) :
    cornerClass Y P hP hne (c • x) = c • cornerClass Y P hP hne x := by
  let q := normMatrixCStarCoronaQuotient
    (fun k ↦ (relabelledCornerModel Y P hP hne k : Type))
  change q (cornerCompressSequence Y P hP hne (c • x)) =
    c • q (cornerCompressSequence Y P hP hne x)
  rw [show cornerCompressSequence Y P hP hne (c • x) =
      c • cornerCompressSequence Y P hP hne x from
    (cornerCompressSequenceLinear Y P hP hne).map_smul c x,
    map_smul]

theorem cornerClass_star
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x : BoundedMatrixSequence (fun n ↦ Y n)) :
    cornerClass Y P hP hne (star x) = star (cornerClass Y P hP hne x) := by
  rw [cornerClass, cornerClass, cornerCompressSequence_star,
    ← normMatrixCStarCorona_star_mk]

theorem cornerClass_sub
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x y : BoundedMatrixSequence (fun n ↦ Y n)) :
    cornerClass Y P hP hne (x - y) =
      cornerClass Y P hP hne x - cornerClass Y P hP hne y := by
  let q := normMatrixCStarCoronaQuotient
    (fun k ↦ (relabelledCornerModel Y P hP hne k : Type))
  change q (cornerCompressSequence Y P hP hne (x - y)) =
    q (cornerCompressSequence Y P hP hne x) -
      q (cornerCompressSequence Y P hP hne y)
  rw [show cornerCompressSequence Y P hP hne (x - y) =
      cornerCompressSequence Y P hP hne x -
        cornerCompressSequence Y P hP hne y from
    (cornerCompressSequenceLinear Y P hP hne).map_sub x y]
  exact q.map_sub _ _

/-- Corner classes depend only on the ambient corona class of a bounded
representative. -/
theorem cornerClass_eq_of_mk_eq
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x y : BoundedMatrixSequence (fun n ↦ Y n))
    (hxy : normMatrixCStarCoronaMk (fun n ↦ Y n) x =
      normMatrixCStarCoronaMk (fun n ↦ Y n) y) :
    cornerClass Y P hP hne x = cornerClass Y P hP hne y := by
  have hnull : IsNullMatrixSequence (fun n ↦ Y n) cofinite (x - y) := by
    rw [← normMatrixCStarCoronaMk_eq_zero_iff, map_sub, hxy, sub_self]
  have hzero := cornerClass_eq_zero_of_isNull Y P hP hne (x - y) hnull
  rw [cornerClass_sub, sub_eq_zero] at hzero
  exact hzero

/-! ## Chosen source lifts and their support sandwiches -/

/-- A chosen bounded lift of the represented source element. -/
def sourceLift
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n)) (a : A) :
    BoundedMatrixSequence (fun n ↦ Y n) :=
  Function.surjInv (normMatrixCStarCoronaMk_surjective (fun n ↦ Y n)) (e a)

omit [Nontrivial A] in
theorem sourceLift_spec
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n)) (a : A) :
    normMatrixCStarCoronaMk (fun n ↦ Y n) (sourceLift Y e a) = e a :=
  Function.surjInv_eq _ (e a)

/-- Sandwich a chosen lift by the projection lift of the support. -/
def sourceSandwich
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (P : BoundedMatrixSequence (fun n ↦ Y n)) (a : A) :
    BoundedMatrixSequence (fun n ↦ Y n) :=
  P * sourceLift Y e a * P

omit [Nontrivial A] in
theorem sourceSandwich_spec
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ Y n) P = supportProjection Y e)
    (a : A) :
    normMatrixCStarCoronaMk (fun n ↦ Y n) (sourceSandwich Y e P a) = e a := by
  exact mk_compress_lift_eq Y e P (sourceLift Y e a) hPmk a
    (sourceLift_spec Y e a)

/-- The source element represented in the relabelled support-corner corona. -/
def sourceCornerClass
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) (a : A) :
    NormMatrixCStarCorona
      (fun k ↦ (relabelledCornerModel Y P hP hne k : Type)) :=
  cornerClass Y P hP hne (sourceSandwich Y e P a)

omit [Nontrivial A] in
theorem sourceCornerClass_zero
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ Y n) P = supportProjection Y e)
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) :
    sourceCornerClass Y e P hP hne 0 = 0 := by
  rw [sourceCornerClass]
  have hclass := cornerClass_eq_of_mk_eq Y P hP hne
    (sourceSandwich Y e P 0) 0 (by
      calc
        normMatrixCStarCoronaMk (fun n ↦ Y n) (sourceSandwich Y e P 0) =
            e 0 := sourceSandwich_spec Y e P hPmk 0
        _ = 0 := e.map_zero
        _ = normMatrixCStarCoronaMk (fun n ↦ Y n) 0 :=
          (map_zero (normMatrixCStarCoronaMk (fun n ↦ Y n))).symm)
  rw [hclass, cornerClass_zero]

omit [Nontrivial A] in
theorem sourceCornerClass_add
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ Y n) P = supportProjection Y e)
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) (a b : A) :
    sourceCornerClass Y e P hP hne (a + b) =
      sourceCornerClass Y e P hP hne a +
        sourceCornerClass Y e P hP hne b := by
  rw [sourceCornerClass, sourceCornerClass, sourceCornerClass]
  have hclass := cornerClass_eq_of_mk_eq Y P hP hne
    (sourceSandwich Y e P (a + b))
    (sourceSandwich Y e P a + sourceSandwich Y e P b) (by
      calc
        normMatrixCStarCoronaMk (fun n ↦ Y n)
            (sourceSandwich Y e P (a + b)) = e (a + b) :=
          sourceSandwich_spec Y e P hPmk (a + b)
        _ = e a + e b := e.map_add a b
        _ = normMatrixCStarCoronaMk (fun n ↦ Y n)
            (sourceSandwich Y e P a) +
              normMatrixCStarCoronaMk (fun n ↦ Y n)
                (sourceSandwich Y e P b) := by
          rw [sourceSandwich_spec Y e P hPmk,
            sourceSandwich_spec Y e P hPmk]
        _ = normMatrixCStarCoronaMk (fun n ↦ Y n)
            (sourceSandwich Y e P a + sourceSandwich Y e P b) :=
          (map_add (normMatrixCStarCoronaMk (fun n ↦ Y n)) _ _).symm)
  rw [hclass, cornerClass_add]

omit [Nontrivial A] in
theorem sourceCornerClass_smul
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ Y n) P = supportProjection Y e)
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (c : ℂ) (a : A) :
    sourceCornerClass Y e P hP hne (c • a) =
      c • sourceCornerClass Y e P hP hne a := by
  rw [sourceCornerClass, sourceCornerClass]
  have hclass := cornerClass_eq_of_mk_eq Y P hP hne
    (sourceSandwich Y e P (c • a)) (c • sourceSandwich Y e P a) (by
      let q := normMatrixCStarCoronaQuotient (fun n ↦ Y n)
      change q (sourceSandwich Y e P (c • a)) =
        q (c • sourceSandwich Y e P a)
      have ha : q (sourceSandwich Y e P a) = e a :=
        sourceSandwich_spec Y e P hPmk a
      calc
        q (sourceSandwich Y e P (c • a)) = e (c • a) :=
          sourceSandwich_spec Y e P hPmk (c • a)
        _ = c • e a := map_smul e c a
        _ = c • q (sourceSandwich Y e P a) :=
          congrArg (fun z ↦ c • z) ha.symm
        _ = q (c • sourceSandwich Y e P a) :=
          (map_smul q c _).symm)
  rw [hclass, cornerClass_smul]

omit [Nontrivial A] in
theorem sourceCornerClass_star
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ Y n) P = supportProjection Y e)
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) (a : A) :
    sourceCornerClass Y e P hP hne (star a) =
      star (sourceCornerClass Y e P hP hne a) := by
  rw [sourceCornerClass, sourceCornerClass]
  have hclass := cornerClass_eq_of_mk_eq Y P hP hne
    (sourceSandwich Y e P (star a)) (star (sourceSandwich Y e P a)) (by
      calc
        normMatrixCStarCoronaMk (fun n ↦ Y n)
            (sourceSandwich Y e P (star a)) = e (star a) :=
          sourceSandwich_spec Y e P hPmk (star a)
        _ = star (e a) := map_star e a
        _ = star (normMatrixCStarCoronaMk (fun n ↦ Y n)
            (sourceSandwich Y e P a)) := by
          rw [sourceSandwich_spec Y e P hPmk]
        _ = normMatrixCStarCoronaMk (fun n ↦ Y n)
            (star (sourceSandwich Y e P a)) :=
          normMatrixCStarCorona_star_mk _ _)
  rw [hclass, cornerClass_star]

omit [Nontrivial A] in
theorem sourceCornerClass_mul
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ Y n) P = supportProjection Y e)
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) (a b : A) :
    sourceCornerClass Y e P hP hne (a * b) =
      sourceCornerClass Y e P hP hne a *
        sourceCornerClass Y e P hP hne b := by
  rw [sourceCornerClass, sourceCornerClass, sourceCornerClass]
  have hclass := cornerClass_eq_of_mk_eq Y P hP hne
    (sourceSandwich Y e P (a * b))
    (sourceSandwich Y e P a * sourceSandwich Y e P b) (by
      calc
        normMatrixCStarCoronaMk (fun n ↦ Y n)
            (sourceSandwich Y e P (a * b)) = e (a * b) :=
          sourceSandwich_spec Y e P hPmk (a * b)
        _ = e a * e b := e.map_mul a b
        _ = normMatrixCStarCoronaMk (fun n ↦ Y n)
              (sourceSandwich Y e P a) *
            normMatrixCStarCoronaMk (fun n ↦ Y n)
              (sourceSandwich Y e P b) := by
          rw [sourceSandwich_spec Y e P hPmk,
            sourceSandwich_spec Y e P hPmk]
        _ = normMatrixCStarCoronaMk (fun n ↦ Y n)
            (sourceSandwich Y e P a * sourceSandwich Y e P b) :=
          (map_mul (normMatrixCStarCoronaMk (fun n ↦ Y n)) _ _).symm)
  rw [hclass, sourceSandwich, sourceSandwich,
    cornerClass_projectionSandwich_mul]

omit [Nontrivial A] in
theorem sourceCornerClass_one
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ Y n) P = supportProjection Y e)
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) :
    sourceCornerClass Y e P hP hne 1 = 1 := by
  rw [sourceCornerClass]
  have hclass := cornerClass_eq_of_mk_eq Y P hP hne
    (sourceSandwich Y e P 1) P (by
      calc
        normMatrixCStarCoronaMk (fun n ↦ Y n) (sourceSandwich Y e P 1) =
            e 1 := sourceSandwich_spec Y e P hPmk 1
        _ = supportProjection Y e := rfl
        _ = normMatrixCStarCoronaMk (fun n ↦ Y n) P := hPmk.symm)
  rw [hclass, cornerClass_projection_eq_one]

/-! ## The unital faithful support-corner representation -/

/-- The support-corner representation, bundled as a unital star-algebra
homomorphism. -/
def supportCornerEmbedding
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ Y n) P = supportProjection Y e)
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) :
    A →⋆ₐ[ℂ] NormMatrixCStarCorona
      (fun k ↦ (relabelledCornerModel Y P hP hne k : Type)) where
  toFun := sourceCornerClass Y e P hP hne
  map_one' := sourceCornerClass_one Y e P hP hPmk hne
  map_mul' := sourceCornerClass_mul Y e P hP hPmk hne
  map_zero' := sourceCornerClass_zero Y e P hP hPmk hne
  map_add' := sourceCornerClass_add Y e P hP hPmk hne
  commutes' c := by
    calc
      sourceCornerClass Y e P hP hne (algebraMap ℂ A c) =
          sourceCornerClass Y e P hP hne (c • (1 : A)) := by
        rw [Algebra.smul_def, mul_one]
      _ = c • sourceCornerClass Y e P hP hne 1 :=
        sourceCornerClass_smul Y e P hP hPmk hne c 1
      _ = c • 1 := by rw [sourceCornerClass_one Y e P hP hPmk hne]
      _ = algebraMap ℂ (NormMatrixCStarCorona
          (fun k ↦ (relabelledCornerModel Y P hP hne k : Type))) c := by
        rw [Algebra.smul_def, mul_one]
  map_star' := sourceCornerClass_star Y e P hP hPmk hne

omit [Nontrivial A] in
@[simp] theorem supportCornerEmbedding_apply
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ Y n) P = supportProjection Y e)
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) (a : A) :
    supportCornerEmbedding Y e P hP hPmk hne a =
      sourceCornerClass Y e P hP hne a :=
  rfl

omit [Nontrivial A] in
theorem supportCornerEmbedding_injective
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (he : Function.Injective e)
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ Y n) P = supportProjection Y e)
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) :
    Function.Injective (supportCornerEmbedding Y e P hP hPmk hne) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply he
  have hcornerZero : sourceCornerClass Y e P hP hne (a - b) = 0 := by
    change supportCornerEmbedding Y e P hP hPmk hne (a - b) = 0
    rw [map_sub, hab, sub_self]
  change normMatrixCStarCoronaMk
      (fun k ↦ (relabelledCornerModel Y P hP hne k : Type))
      (cornerCompressSequence Y P hP hne
        (sourceSandwich Y e P (a - b))) = 0 at hcornerZero
  have hnullCorner : IsNullMatrixSequence
      (fun k ↦ (relabelledCornerModel Y P hP hne k : Type)) cofinite
      (cornerCompressSequence Y P hP hne
        (sourceSandwich Y e P (a - b))) := by
    exact (normMatrixCStarCoronaMk_eq_zero_iff
      (fun k ↦ (relabelledCornerModel Y P hP hne k : Type)) _).mp hcornerZero
  have hnullAmbient : IsNullMatrixSequence (fun n ↦ Y n) cofinite
      (sourceSandwich Y e P (a - b)) := by
    exact (isNull_cornerCompressSequence_projectionSandwich_iff Y P hP hne
      (sourceLift Y e (a - b))).mp hnullCorner
  have hmkzero : normMatrixCStarCoronaMk (fun n ↦ Y n)
      (sourceSandwich Y e P (a - b)) = 0 :=
    (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ Y n) _).mpr hnullAmbient
  have hezero : e (a - b) = 0 := by
    rw [← sourceSandwich_spec Y e P hPmk]
    exact hmkzero
  simpa using hezero

/-- Every injective, possibly nonunital norm-matrix-corona representation of a
unital C-star algebra yields an injective unital representation into the
corona of the relabelled finite projection ranges. -/
theorem exists_injective_unital_supportCornerEmbedding
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (he : Function.Injective e) :
    ∃ Z : ℕ → FiniteModel, ∃ hZne : ∀ n, Nonempty (Z n),
      letI : ∀ n, Nonempty (Z n) := hZne
      ∃ E : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n),
        Function.Injective E := by
  obtain ⟨P, hP, hPmk, _hPinfinite⟩ :=
    exists_projection_lift_with_infinite_support Y e he
  have hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0 := by
    rw [hPmk]
    exact supportProjection_ne_zero Y e he
  let Z : ℕ → FiniteModel := fun k ↦ relabelledCornerModel Y P hP hne k
  let hZne : ∀ n, Nonempty (Z n) := fun k ↦
    relabelledCornerModel_nonempty Y P hP hne k
  refine ⟨Z, hZne, supportCornerEmbedding Y e P hP hPmk hne, ?_⟩
  exact supportCornerEmbedding_injective Y e he P hP hPmk hne

#audit_axioms cornerClass_eq_of_mk_eq
#audit_axioms sourceSandwich_spec
#audit_axioms supportCornerEmbedding
#audit_axioms supportCornerEmbedding_injective
#audit_axioms exists_injective_unital_supportCornerEmbedding

end

end NonUnitalMFSupportCornerEmbedding
end GroupApproximation
