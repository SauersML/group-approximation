import GroupApproximation.Manuscript.MFRecognition.HNNPermanence

/-!
# `thm:hnn-permanence` with a possibly nonunital corona embedding

The printed hypothesis of `thm:hnn-permanence` is *"an injective
`*`-homomorphism `ι : A → 𝒬` and a unitary `W ∈ 𝒬`"*; unitality of `ι` is not
assumed.  The unital form of the theorem is
`HNNPermanence.manuscriptHNNPermanence`.  This module carries out the printed
passage from that form to the nonunital one.

Write `p = ι(1)` for the support projection.  The covariance hypothesis at
`s = 1` reads `W p W* = p`, so `W` commutes with `p`, and both `ι` and `W`
compress to the corner `p𝒬p`.  That corner is again a norm matrix corona: it
is the relabelled support-corner corona of
`NonUnitalMFSupportCornerEmbedding`, in which `ι` becomes the injective
*unital* embedding `supportCornerEmbedding`.

The compression of an ambient corona element is `coronaCornerClass`.  It is
not multiplicative on all of `𝒬`, so the products it does preserve are
isolated as `coronaCornerClass_mul`: those already sandwiched by `p`.  The
compression of `W` is then a unitary of the corner implementing the same
covariance, and the unital theorem applies to it.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanenceNonunital

open Matrix
open GroupApproximation.KazhdanCornerMatrices
open GroupApproximation.NonUnitalMFSupportCorner
open GroupApproximation.NonUnitalMFSupportCornerEmbedding
open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

/-! ## Sandwich identities

The four ring identities used below, isolated from the corona so that they
are proved once by associativity and the two structural hypotheses
`p * p = p` and `p * w = w * p`. -/

section Sandwich

variable {R : Type*} [Ring R] {p w : R}

/-- Two sandwiches by an idempotent multiply as one sandwiched product. -/
theorem sandwich_mul_sandwich (hpp : p * p = p) (a b : R) :
    p * a * p * (p * b * p) = p * a * p * b * p := by
  calc p * a * p * (p * b * p) = p * a * (p * p) * b * p := by noncomm_ring
    _ = p * a * p * b * p := by rw [hpp]

/-- A left factor commuting with the idempotent leaves the sandwich. -/
theorem sandwich_left_comm (hpp : p * p = p) (hwp : p * w = w * p) (a : R) :
    p * w * p * a * p = p * (w * a) * p := by
  calc p * w * p * a * p = (p * w) * (p * (a * p)) := by noncomm_ring
    _ = (w * p) * (p * (a * p)) := by rw [hwp]
    _ = w * (p * p) * (a * p) := by noncomm_ring
    _ = w * p * (a * p) := by rw [hpp]
    _ = (p * w) * (a * p) := by rw [hwp]
    _ = p * (w * a) * p := by noncomm_ring

/-- A right factor commuting with the idempotent leaves the sandwich. -/
theorem sandwich_right_comm (hpp : p * p = p) (hwp : p * w = w * p) (a : R) :
    p * a * p * w * p = p * (a * w) * p := by
  calc p * a * p * w * p = (p * a) * ((p * w) * p) := by noncomm_ring
    _ = (p * a) * ((w * p) * p) := by rw [hwp]
    _ = (p * a) * (w * (p * p)) := by noncomm_ring
    _ = (p * a) * (w * p) := by rw [hpp]
    _ = p * (a * w) * p := by noncomm_ring

/-- The adjoint of an element commuting with a self-adjoint idempotent
commutes with it as well. -/
theorem star_comm_of_comm {R : Type*} [Ring R] [StarRing R] {p w : R}
    (hp : star p = p) (hwp : p * w = w * p) : p * star w = star w * p := by
  have h := congrArg star hwp
  rw [star_mul, star_mul, hp] at h
  exact h.symm

end Sandwich

variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]

/-! ## The compression of an ambient corona element -/

/-- A chosen bounded lift of an ambient corona element. -/
def coronaLift (q : NormMatrixCStarCorona (fun n ↦ Y n)) :
    BoundedMatrixSequence (fun n ↦ Y n) :=
  Function.surjInv (normMatrixCStarCoronaMk_surjective (fun n ↦ Y n)) q

@[simp] theorem coronaLift_spec (q : NormMatrixCStarCorona (fun n ↦ Y n)) :
    normMatrixCStarCoronaMk (fun n ↦ Y n) (coronaLift Y q) = q :=
  Function.surjInv_eq _ q

omit [∀ n, Nonempty (Y n)] in
/-- A lift by orthogonal projection matrices is self-adjoint. -/
theorem star_projectionLift
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n)) :
    star P = P := by
  refine lp.ext (funext fun n ↦ ?_)
  change ((P n : Matrix (Y n) (Y n) ℂ))ᴴ = P n
  exact (hP n).1

omit [∀ n, Nonempty (Y n)] in
/-- A lift by orthogonal projection matrices is idempotent. -/
theorem projectionLift_mul_self
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n)) :
    P * P = P := by
  refine lp.ext (funext fun n ↦ ?_)
  change (P n : Matrix (Y n) (Y n) ℂ) * P n = P n
  exact (hP n).2

/-- The corona element carried by a projection lift is self-adjoint. -/
theorem star_mk_projectionLift
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n)) :
    star (normMatrixCStarCoronaMk (fun n ↦ Y n) P) =
      normMatrixCStarCoronaMk (fun n ↦ Y n) P := by
  rw [normMatrixCStarCorona_star_mk, star_projectionLift Y P hP]

/-- The corona element carried by a projection lift is idempotent. -/
theorem mk_projectionLift_mul_self
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n)) :
    normMatrixCStarCoronaMk (fun n ↦ Y n) P *
        normMatrixCStarCoronaMk (fun n ↦ Y n) P =
      normMatrixCStarCoronaMk (fun n ↦ Y n) P := by
  rw [← map_mul, projectionLift_mul_self Y P hP]

/-- The compression of an ambient corona element to the relabelled
support-corner corona. -/
def coronaCornerClass
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (q : NormMatrixCStarCorona (fun n ↦ Y n)) :
    NormMatrixCStarCorona
      (fun k ↦ (relabelledCornerModel Y P hP hne k : Type)) :=
  cornerClass Y P hP hne (P * coronaLift Y q * P)

/-- The compression is computed by any bounded representative. -/
theorem coronaCornerClass_mk
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x : BoundedMatrixSequence (fun n ↦ Y n)) :
    coronaCornerClass Y P hP hne (normMatrixCStarCoronaMk (fun n ↦ Y n) x) =
      cornerClass Y P hP hne (P * x * P) := by
  rw [coronaCornerClass]
  refine cornerClass_eq_of_mk_eq Y P hP hne _ _ ?_
  simp only [map_mul, coronaLift_spec]

/-- The compression respects adjoints. -/
theorem star_coronaCornerClass
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (q : NormMatrixCStarCorona (fun n ↦ Y n)) :
    star (coronaCornerClass Y P hP hne q) =
      coronaCornerClass Y P hP hne (star q) := by
  have hstarp := star_mk_projectionLift Y P hP
  rw [coronaCornerClass, coronaCornerClass, ← cornerClass_star]
  refine cornerClass_eq_of_mk_eq Y P hP hne _ _ ?_
  rw [← normMatrixCStarCorona_star_mk]
  simp only [map_mul, coronaLift_spec]
  rw [star_mul, star_mul, hstarp, mul_assoc]

/-- **The products the compression preserves.**  If the sandwiched product of
`q₁` and `q₂` is the sandwich of `q₃`, then the compressions multiply
accordingly.  Compression is not multiplicative on all of the corona. -/
theorem coronaCornerClass_mul
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (q₁ q₂ q₃ : NormMatrixCStarCorona (fun n ↦ Y n))
    (h : normMatrixCStarCoronaMk (fun n ↦ Y n) P * q₁ *
            normMatrixCStarCoronaMk (fun n ↦ Y n) P * q₂ *
            normMatrixCStarCoronaMk (fun n ↦ Y n) P =
          normMatrixCStarCoronaMk (fun n ↦ Y n) P * q₃ *
            normMatrixCStarCoronaMk (fun n ↦ Y n) P) :
    coronaCornerClass Y P hP hne q₁ * coronaCornerClass Y P hP hne q₂ =
      coronaCornerClass Y P hP hne q₃ := by
  have hpp := mk_projectionLift_mul_self Y P hP
  rw [coronaCornerClass, coronaCornerClass, coronaCornerClass,
    ← cornerClass_projectionSandwich_mul]
  refine cornerClass_eq_of_mk_eq Y P hP hne _ _ ?_
  simp only [map_mul, coronaLift_spec]
  rw [sandwich_mul_sandwich hpp]
  exact h

/-- An element whose sandwich is the projection compresses to the unit. -/
theorem coronaCornerClass_eq_one
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (q : NormMatrixCStarCorona (fun n ↦ Y n))
    (h : normMatrixCStarCoronaMk (fun n ↦ Y n) P * q *
          normMatrixCStarCoronaMk (fun n ↦ Y n) P =
        normMatrixCStarCoronaMk (fun n ↦ Y n) P) :
    coronaCornerClass Y P hP hne q = 1 := by
  rw [coronaCornerClass]
  have hclass : cornerClass Y P hP hne (P * coronaLift Y q * P) =
      cornerClass Y P hP hne P := by
    refine cornerClass_eq_of_mk_eq Y P hP hne _ _ ?_
    simpa only [map_mul, coronaLift_spec] using h
  rw [hclass, cornerClass_projection_eq_one]

/-- The compression is unital. -/
@[simp] theorem coronaCornerClass_one
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) :
    coronaCornerClass Y P hP hne 1 = 1 := by
  refine coronaCornerClass_eq_one Y P hP hne 1 ?_
  rw [mul_one]
  exact mk_projectionLift_mul_self Y P hP

/-! ## Compressing a unitary which commutes with the support -/

/-- The compression of a unitary commuting with the support projection is a
coisometry. -/
theorem coronaCornerClass_mul_star_self
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (w : NormMatrixCStarCorona (fun n ↦ Y n))
    (hwp : normMatrixCStarCoronaMk (fun n ↦ Y n) P * w =
      w * normMatrixCStarCoronaMk (fun n ↦ Y n) P)
    (hw : w * star w = 1) :
    coronaCornerClass Y P hP hne w *
        star (coronaCornerClass Y P hP hne w) = 1 := by
  have hpp := mk_projectionLift_mul_self Y P hP
  rw [star_coronaCornerClass]
  refine (coronaCornerClass_mul Y P hP hne w (star w) 1 ?_).trans
    (coronaCornerClass_one Y P hP hne)
  calc normMatrixCStarCoronaMk (fun n ↦ Y n) P * w *
          normMatrixCStarCoronaMk (fun n ↦ Y n) P * star w *
          normMatrixCStarCoronaMk (fun n ↦ Y n) P =
        normMatrixCStarCoronaMk (fun n ↦ Y n) P * (w * star w) *
          normMatrixCStarCoronaMk (fun n ↦ Y n) P :=
      sandwich_left_comm hpp hwp (star w)
    _ = normMatrixCStarCoronaMk (fun n ↦ Y n) P * 1 *
        normMatrixCStarCoronaMk (fun n ↦ Y n) P := by rw [hw]

/-- The compression of a unitary commuting with the support projection is an
isometry. -/
theorem coronaCornerClass_star_mul_self
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (w : NormMatrixCStarCorona (fun n ↦ Y n))
    (hwp : normMatrixCStarCoronaMk (fun n ↦ Y n) P * w =
      w * normMatrixCStarCoronaMk (fun n ↦ Y n) P)
    (hw : star w * w = 1) :
    star (coronaCornerClass Y P hP hne w) *
        coronaCornerClass Y P hP hne w = 1 := by
  have hpp := mk_projectionLift_mul_self Y P hP
  rw [star_coronaCornerClass]
  refine (coronaCornerClass_mul Y P hP hne (star w) w 1 ?_).trans
    (coronaCornerClass_one Y P hP hne)
  calc normMatrixCStarCoronaMk (fun n ↦ Y n) P * star w *
          normMatrixCStarCoronaMk (fun n ↦ Y n) P * w *
          normMatrixCStarCoronaMk (fun n ↦ Y n) P =
        normMatrixCStarCoronaMk (fun n ↦ Y n) P * (star w * w) *
          normMatrixCStarCoronaMk (fun n ↦ Y n) P :=
      sandwich_right_comm hpp hwp (star w)
    _ = normMatrixCStarCoronaMk (fun n ↦ Y n) P * 1 *
        normMatrixCStarCoronaMk (fun n ↦ Y n) P := by rw [hw]

/-- **The compression transports conjugation.**  A unitary commuting with the
support projection conjugates compressions exactly as it conjugates in the
ambient corona. -/
theorem coronaCornerClass_conj
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (w q : NormMatrixCStarCorona (fun n ↦ Y n))
    (hwp : normMatrixCStarCoronaMk (fun n ↦ Y n) P * w =
      w * normMatrixCStarCoronaMk (fun n ↦ Y n) P) :
    coronaCornerClass Y P hP hne w * coronaCornerClass Y P hP hne q *
        star (coronaCornerClass Y P hP hne w) =
      coronaCornerClass Y P hP hne (w * q * star w) := by
  have hpp := mk_projectionLift_mul_self Y P hP
  have hswp := star_comm_of_comm (star_mk_projectionLift Y P hP) hwp
  rw [star_coronaCornerClass,
    coronaCornerClass_mul Y P hP hne w q (w * q)
      (sandwich_left_comm hpp hwp q)]
  exact coronaCornerClass_mul Y P hP hne (w * q) (star w) (w * q * star w)
    (sandwich_right_comm hpp hswp (w * q))

/-- On the represented algebra the compression is the unital support-corner
embedding. -/
theorem coronaCornerClass_supportCornerEmbedding
    {A : Type u} [CStarAlgebra A] [Nontrivial A]
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ Y n) P = supportProjection Y e)
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) (a : A) :
    coronaCornerClass Y P hP hne (e a) =
      supportCornerEmbedding Y e P hP hPmk hne a := by
  rw [supportCornerEmbedding_apply, coronaCornerClass, sourceCornerClass]
  refine cornerClass_eq_of_mk_eq Y P hP hne _ _ ?_
  rw [sourceSandwich_spec Y e P hPmk]
  simp only [map_mul, coronaLift_spec, hPmk]
  rw [supportProjection_mul_apply, apply_mul_supportProjection]

/-! ## `thm:hnn-permanence`, printed form -/

/-- **`thm:hnn-permanence` with a possibly nonunital `ι`.**

Printed: *"for some norm matrix corona `𝒬` there are an injective
`*`-homomorphism `ι : A → 𝒬` and a unitary `W ∈ 𝒬` with
`W ιρ(s) W* = ιρ(θ(s))`."*  Unitality of `ι` is not assumed.

Proof: the covariance at `s = 1` says `W ι(1) W* = ι(1)`, so `W` commutes with
the support projection `p = ι(1)`.  Compressing to the corner `p𝒬p`, which is
the relabelled support-corner corona, makes `ι` unital and injective and `W`
a unitary implementing the same covariance, and the unital form
`HNNPermanence.manuscriptHNNPermanence` applies. -/
theorem manuscriptHNNPermanence_nonunital (hIn : HNNPermanence.HNNInputs)
    {G : Type} [Group G] [Countable G]
    {S T : Subgroup G} (phi : S ≃* T)
    {A : Type} [CStarAlgebra A] (realization : RegularRealizationData G A)
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (iota : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (hiota : Function.Injective iota)
    (W : unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (hW : ∀ s : S,
      (W : NormMatrixCStarCorona (fun n ↦ X n)) *
            iota ((realization.rho (s : G) : unitary A) : A) *
          star (W : NormMatrixCStarCorona (fun n ↦ X n)) =
        iota ((realization.rho ((phi s : T) : G) : unitary A) : A)) :
    IsRegularlyRealized (HNNExtension G S T phi) := by
  letI : Nontrivial A :=
    OneSidedMFRadical.TensorSynchronizationAssembly.regularRealization_nontrivial
      realization
  obtain ⟨P, hP, hPmk, _hinfinite⟩ :=
    exists_projection_lift_with_infinite_support X iota hiota
  have hne : normMatrixCStarCoronaMk (fun n ↦ X n) P ≠ 0 := by
    rw [hPmk]
    exact supportProjection_ne_zero X iota hiota
  have hp : normMatrixCStarCoronaMk (fun n ↦ X n) P = iota 1 := hPmk
  -- The covariance at `s = 1`: `W` commutes with the support projection.
  have hone : ((realization.rho ((1 : S) : G) : unitary A) : A) = 1 := by
    simp
  have honephi : ((realization.rho ((phi 1 : T) : G) : unitary A) : A) = 1 := by
    simp
  have hWone : (W : NormMatrixCStarCorona (fun n ↦ X n)) * iota 1 *
      star (W : NormMatrixCStarCorona (fun n ↦ X n)) = iota 1 := by
    have h := hW 1
    rwa [hone, honephi] at h
  have hwp : normMatrixCStarCoronaMk (fun n ↦ X n) P *
      (W : NormMatrixCStarCorona (fun n ↦ X n)) =
        (W : NormMatrixCStarCorona (fun n ↦ X n)) *
          normMatrixCStarCoronaMk (fun n ↦ X n) P := by
    rw [hp]
    calc iota 1 * (W : NormMatrixCStarCorona (fun n ↦ X n)) =
          (W : NormMatrixCStarCorona (fun n ↦ X n)) * iota 1 *
            star (W : NormMatrixCStarCorona (fun n ↦ X n)) *
            (W : NormMatrixCStarCorona (fun n ↦ X n)) := by rw [hWone]
      _ = (W : NormMatrixCStarCorona (fun n ↦ X n)) * iota 1 *
            (star (W : NormMatrixCStarCorona (fun n ↦ X n)) *
              (W : NormMatrixCStarCorona (fun n ↦ X n))) := by noncomm_ring
      _ = (W : NormMatrixCStarCorona (fun n ↦ X n)) * iota 1 := by
          rw [Unitary.star_mul_self_of_mem W.2, mul_one]
  -- The compressed unitary.
  have hmem : coronaCornerClass X P hP hne
      (W : NormMatrixCStarCorona (fun n ↦ X n)) ∈
      unitary (NormMatrixCStarCorona
        (fun k ↦ (relabelledCornerModel X P hP hne k : Type))) := by
    rw [Unitary.mem_iff]
    exact ⟨coronaCornerClass_star_mul_self X P hP hne _ hwp
        (Unitary.star_mul_self_of_mem W.2),
      coronaCornerClass_mul_star_self X P hP hne _ hwp
        (Unitary.mul_star_self_of_mem W.2)⟩
  refine HNNPermanence.manuscriptHNNPermanence hIn phi realization
    (supportCornerEmbedding X iota P hP hPmk hne)
    (supportCornerEmbedding_injective X iota hiota P hP hPmk hne)
    ⟨_, hmem⟩ ?_
  intro s
  show coronaCornerClass X P hP hne
        (W : NormMatrixCStarCorona (fun n ↦ X n)) *
      supportCornerEmbedding X iota P hP hPmk hne
        ((realization.rho (s : G) : unitary A) : A) *
      star (coronaCornerClass X P hP hne
        (W : NormMatrixCStarCorona (fun n ↦ X n))) =
    supportCornerEmbedding X iota P hP hPmk hne
      ((realization.rho ((phi s : T) : G) : unitary A) : A)
  rw [← coronaCornerClass_supportCornerEmbedding X iota P hP hPmk hne,
    ← coronaCornerClass_supportCornerEmbedding X iota P hP hPmk hne,
    coronaCornerClass_conj X P hP hne _ _ hwp, hW s]

end

end HNNPermanenceNonunital
end MFRecognition
end Manuscript
end GroupApproximation
