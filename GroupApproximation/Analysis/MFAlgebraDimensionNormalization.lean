import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Sofic.OperatorMFIncreasingDimensions

/-!
# The MF definition does not depend on the dimension sequence

The manuscript defines the corona over an arbitrary sequence of positive matrix
sizes,

`Q((d_n)) = ∏_n M_{d_n}(ℂ) / ⨁_n M_{d_n}(ℂ)`,  `d_n > 0`,

calls a separable `C*`-algebra **MF** when it embeds into some such `Q((d_n))`
(Blackadar--Kirchberg), and then records a convention:

> Proposition `prop:mf-equivalences` shows that nothing changes if the
> dimensions are required to be strictly increasing.

`Analysis/MFAlgebra.HasMFEmbedding` builds `StrictMono (Fintype.card ∘ X)` into
the *definition*, and `Sofic/OperatorMFIncreasingDimensions` proves the
normalization only for the **group** predicate `IsOperatorMF`.  So at the
algebra level the printed definition was the unrestricted one and the formal
definition was the normalized one, with nothing between them.

This file supplies what is between them.  `HasUnrestrictedMFEmbedding` is the
printed definition verbatim -- an arbitrary sequence of nonempty finite models,
no monotonicity -- and `hasMFEmbedding_iff` proves it equivalent to
`HasMFEmbedding`.  `isMFAlgebra_iff` is the same statement for the
literature-standard predicate, separability included.

## The construction

The normalization is the algebra-level counterpart of
`OperatorMFIncreasingDimensions`, and it uses the same cumulative model
`increasingBlockModel X n = X 0 ⊕ ⋯ ⊕ X n`, whose dimensions strictly increase
because every `X n` is nonempty.  Where the group file puts the `n`th unitary in
the newest summand and the *identity* on the earlier ones -- the only choice
that is a group homomorphism -- an algebra map must put **zero** there:

`cornerCoord X (n+1) a = blockDiag 0 a`.

This is a nonunital `⋆`-homomorphism, which is exactly what `HasMFEmbedding`
allows ("The embedding need not be unital"), and it is isometric because
`l2_opNorm_blockDiag` computes the operator norm of a block diagonal as the
maximum of the two block norms and `‖0‖ = 0`.

Isometry is what makes the induced map on coronas **injective**: a sequence is
null exactly when its image is, so the corner map neither creates nor destroys
elements of the null ideal.  The induced map is built by choosing a lift with
`Function.surjInv` and proving the computation rule `cornerCorona_mk` -- two
lifts of the same class differ by a null sequence, whose corner image is null --
after which every algebraic identity is checked on lifts.

## What is assumed

Nothing.  The equivalence is unconditional and holds for every non-unital
`C*`-algebra; positivity of the dimensions is part of the printed definition on
both sides and is not an extra hypothesis.
-/

namespace GroupApproximation
namespace MFAlgebraDimension

open Filter
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

/-! ## Block diagonals, in the directions `NormMFUniversalCorona` did not need -/

theorem blockDiagMatrix_zero (Y Z : FiniteModel) :
    blockDiagMatrix Y Z (0 : Matrix Y Y ℂ) (0 : Matrix Z Z ℂ) = 0 := by
  ext p q
  cases p <;> cases q <;>
    simp [blockDiagMatrix, Matrix.fromBlocks]

theorem blockDiagMatrix_add (Y Z : FiniteModel)
    (A C : Matrix Y Y ℂ) (B D : Matrix Z Z ℂ) :
    blockDiagMatrix Y Z A B + blockDiagMatrix Y Z C D =
      blockDiagMatrix Y Z (A + C) (B + D) := by
  ext p q
  cases p <;> cases q <;>
    simp [blockDiagMatrix, Matrix.fromBlocks, Matrix.add_apply]

theorem blockDiagMatrix_smul (Y Z : FiniteModel) (c : ℂ)
    (A : Matrix Y Y ℂ) (B : Matrix Z Z ℂ) :
    c • blockDiagMatrix Y Z A B = blockDiagMatrix Y Z (c • A) (c • B) := by
  ext p q
  cases p <;> cases q <;>
    simp [blockDiagMatrix, Matrix.fromBlocks, Matrix.smul_apply]

/-! ## The corner coordinate maps -/

variable (X : ℕ → FiniteModel)

/-- The `n`th block placed in the newest summand of the cumulative model, with
zero on the earlier summands.  At `n = 0` the cumulative model *is* `X 0`, and
the map is the identity.

Contrast `OperatorMFIncreasingDimensions.increasingCoordinateEmbed`, which puts
the identity on the earlier summands: that is forced for a group homomorphism
and forbidden for an algebra homomorphism. -/
def cornerCoord : ∀ n, Matrix (X n) (X n) ℂ →
    Matrix (increasingBlockModel X n) (increasingBlockModel X n) ℂ
  | 0 => id
  | n + 1 => fun a =>
      blockDiagMatrix (increasingBlockModel X n) (X (n + 1)) 0 a

@[simp]
theorem cornerCoord_zero_apply (a : Matrix (X 0) (X 0) ℂ) :
    cornerCoord X 0 a = a := rfl

@[simp]
theorem cornerCoord_succ_apply (n : ℕ) (a : Matrix (X (n + 1)) (X (n + 1)) ℂ) :
    cornerCoord X (n + 1) a =
      blockDiagMatrix (increasingBlockModel X n) (X (n + 1)) 0 a := rfl

theorem cornerCoord_map_zero (n : ℕ) : cornerCoord X n 0 = 0 := by
  cases n with
  | zero => rfl
  | succ n => exact blockDiagMatrix_zero _ _

theorem cornerCoord_map_add (n : ℕ) (a b : Matrix (X n) (X n) ℂ) :
    cornerCoord X n (a + b) = cornerCoord X n a + cornerCoord X n b := by
  cases n with
  | zero => rfl
  | succ n =>
      have h := blockDiagMatrix_add (increasingBlockModel X n) (X (n + 1))
        0 0 a b
      rw [add_zero] at h
      exact h.symm

theorem cornerCoord_map_sub (n : ℕ) (a b : Matrix (X n) (X n) ℂ) :
    cornerCoord X n (a - b) = cornerCoord X n a - cornerCoord X n b := by
  cases n with
  | zero => rfl
  | succ n =>
      have h := blockDiagMatrix_sub (increasingBlockModel X n) (X (n + 1))
        0 0 a b
      rw [sub_zero] at h
      exact h.symm

theorem cornerCoord_map_mul (n : ℕ) (a b : Matrix (X n) (X n) ℂ) :
    cornerCoord X n (a * b) = cornerCoord X n a * cornerCoord X n b := by
  cases n with
  | zero => rfl
  | succ n =>
      have h := blockDiagMatrix_mul (increasingBlockModel X n) (X (n + 1))
        0 0 a b
      rw [mul_zero] at h
      exact h.symm

theorem cornerCoord_map_smul (n : ℕ) (c : ℂ) (a : Matrix (X n) (X n) ℂ) :
    cornerCoord X n (c • a) = c • cornerCoord X n a := by
  cases n with
  | zero => rfl
  | succ n =>
      have h := blockDiagMatrix_smul (increasingBlockModel X n) (X (n + 1))
        c 0 a
      rw [smul_zero] at h
      exact h.symm

theorem cornerCoord_map_star (n : ℕ) (a : Matrix (X n) (X n) ℂ) :
    cornerCoord X n (star a) = star (cornerCoord X n a) := by
  cases n with
  | zero => rfl
  | succ n =>
      have h := blockDiagMatrix_conjTranspose (increasingBlockModel X n)
        (X (n + 1)) 0 a
      rw [Matrix.conjTranspose_zero] at h
      exact h.symm

/-- **The corner map is isometric.**  This is the whole reason the induced map
on coronas is injective. -/
theorem norm_cornerCoord (n : ℕ) (a : Matrix (X n) (X n) ℂ) :
    ‖cornerCoord X n a‖ = ‖a‖ := by
  cases n with
  | zero => rfl
  | succ n =>
      have h := l2_opNorm_blockDiag (increasingBlockModel X n) (X (n + 1))
        (0 : Matrix (increasingBlockModel X n) (increasingBlockModel X n) ℂ) a
      rw [norm_zero, max_eq_right (norm_nonneg a)] at h
      exact h

/-! ## Nonemptiness of the cumulative models -/

theorem nonempty_increasingBlockModel (hne : ∀ n, Nonempty (X n)) :
    ∀ n, Nonempty (increasingBlockModel X n)
  | 0 => hne 0
  | n + 1 =>
      Nonempty.elim (nonempty_increasingBlockModel hne n) fun y ↦ ⟨Sum.inl y⟩

instance instNonemptyIncreasingBlockModel [h : ∀ n, Nonempty (X n)] (n : ℕ) :
    Nonempty (increasingBlockModel X n) :=
  nonempty_increasingBlockModel X h n

theorem card_increasingBlockModel_pos [∀ n, Nonempty (X n)] (n : ℕ) :
    0 < Fintype.card (increasingBlockModel X n) :=
  Fintype.card_pos_iff.mpr inferInstance

/-! ## The corner map on bounded sequences -/

variable [∀ n, Nonempty (X n)]

/-- The corner map on bounded matrix sequences: coordinatewise `cornerCoord`.
It is bounded because each coordinate map is isometric. -/
def cornerSeq (a : BoundedMatrixSequence (fun n ↦ X n)) :
    BoundedMatrixSequence (fun n ↦ increasingBlockModel X n) :=
  ⟨fun n ↦ cornerCoord X n (a n), memℓp_infty ⟨‖a‖, by
    rintro _ ⟨n, rfl⟩
    exact (norm_cornerCoord X n (a n)).le.trans
      (boundedMatrixSequence_coord_norm_le (fun n ↦ X n) a n)⟩⟩

omit [∀ (n : ℕ), Nonempty (X n).carrier] in
@[simp] theorem cornerSeq_apply (a : BoundedMatrixSequence (fun n ↦ X n))
    (n : ℕ) : cornerSeq X a n = cornerCoord X n (a n) := rfl

omit [∀ (n : ℕ), Nonempty (X n).carrier] in
theorem cornerSeq_zero : cornerSeq X 0 = 0 := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [lp.coeFn_zero, Pi.zero_apply]
  exact cornerCoord_map_zero X n

omit [∀ (n : ℕ), Nonempty (X n).carrier] in
theorem cornerSeq_add (a b : BoundedMatrixSequence (fun n ↦ X n)) :
    cornerSeq X (a + b) = cornerSeq X a + cornerSeq X b := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [lp.coeFn_add, Pi.add_apply]
  exact cornerCoord_map_add X n (a n) (b n)

omit [∀ (n : ℕ), Nonempty (X n).carrier] in
theorem cornerSeq_sub (a b : BoundedMatrixSequence (fun n ↦ X n)) :
    cornerSeq X (a - b) = cornerSeq X a - cornerSeq X b := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [lp.coeFn_sub, Pi.sub_apply]
  exact cornerCoord_map_sub X n (a n) (b n)

omit [∀ (n : ℕ), Nonempty (X n).carrier] in
theorem cornerSeq_mul (a b : BoundedMatrixSequence (fun n ↦ X n)) :
    cornerSeq X (a * b) = cornerSeq X a * cornerSeq X b := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [lp.infty_coeFn_mul, Pi.mul_apply]
  exact cornerCoord_map_mul X n (a n) (b n)

theorem cornerSeq_smul (c : ℂ) (a : BoundedMatrixSequence (fun n ↦ X n)) :
    cornerSeq X (c • a) = c • cornerSeq X a := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [lp.coeFn_smul, Pi.smul_apply]
  exact cornerCoord_map_smul X n c (a n)

omit [∀ (n : ℕ), Nonempty (X n).carrier] in
theorem cornerSeq_star (a : BoundedMatrixSequence (fun n ↦ X n)) :
    cornerSeq X (star a) = star (cornerSeq X a) := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [lp.coeFn_star, Pi.star_apply]
  exact cornerCoord_map_star X n (a n)

omit [∀ (n : ℕ), Nonempty (X n).carrier] in
/-- **Isometry, at the level of sequences.**  The corner map neither creates nor
destroys null sequences, which is what makes the induced corona map injective
rather than merely well defined. -/
theorem isNull_cornerSeq_iff (l : Filter ℕ)
    (a : BoundedMatrixSequence (fun n ↦ X n)) :
    IsNullMatrixSequence (fun n ↦ increasingBlockModel X n) l (cornerSeq X a)
      ↔ IsNullMatrixSequence (fun n ↦ X n) l a := by
  have hfun : (fun n ↦ ‖cornerSeq X a n‖) = fun n ↦ ‖a n‖ := by
    funext n
    rw [cornerSeq_apply, norm_cornerCoord]
  show Tendsto (fun n ↦ ‖cornerSeq X a n‖) l (nhds 0)
    ↔ Tendsto (fun n ↦ ‖a n‖) l (nhds 0)
  rw [hfun]

/-! ## The corner map on coronas -/

/-- The quotient map is `ℂ`-linear, read off the bundled `⋆`-algebra form. -/
theorem normMatrixCStarCoronaMk_smul (Z : ℕ → Type) [∀ n, Fintype (Z n)]
    [∀ n, DecidableEq (Z n)] [∀ n, Nonempty (Z n)] (c : ℂ)
    (a : BoundedMatrixSequence Z) :
    normMatrixCStarCoronaMk Z (c • a) = c • normMatrixCStarCoronaMk Z a :=
  map_smul (normMatrixCStarCoronaQuotient Z) c a

/-- A chosen representative of a corona class. -/
def coronaLift (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    BoundedMatrixSequence (fun n ↦ X n) :=
  Function.surjInv (normMatrixCStarCoronaMk_surjective (fun n ↦ X n)) x

theorem coronaLift_spec (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    normMatrixCStarCoronaMk (fun n ↦ X n) (coronaLift X x) = x :=
  Function.surjInv_eq _ x

/-- The corner map on coronas, defined on a chosen lift. -/
def cornerCorona (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    NormMatrixCStarCorona (fun n ↦ increasingBlockModel X n) :=
  normMatrixCStarCoronaMk (fun n ↦ increasingBlockModel X n)
    (cornerSeq X (coronaLift X x))

/-- **Well-definedness.**  Two lifts of the same class differ by a null
sequence, and the corner map carries null sequences to null sequences, so the
choice of lift does not matter. -/
theorem cornerCorona_mk (a : BoundedMatrixSequence (fun n ↦ X n)) :
    cornerCorona X (normMatrixCStarCoronaMk (fun n ↦ X n) a) =
      normMatrixCStarCoronaMk (fun n ↦ increasingBlockModel X n)
        (cornerSeq X a) := by
  have hb : normMatrixCStarCoronaMk (fun n ↦ X n)
      (coronaLift X (normMatrixCStarCoronaMk (fun n ↦ X n) a))
      = normMatrixCStarCoronaMk (fun n ↦ X n) a :=
    coronaLift_spec X _
  have hnull : IsNullMatrixSequence (fun n ↦ X n) cofinite
      (coronaLift X (normMatrixCStarCoronaMk (fun n ↦ X n) a) - a) := by
    rw [← normMatrixCStarCoronaMk_eq_zero_iff, map_sub, hb, sub_self]
  have hnull' : IsNullMatrixSequence (fun n ↦ increasingBlockModel X n) cofinite
      (cornerSeq X (coronaLift X (normMatrixCStarCoronaMk (fun n ↦ X n) a))
        - cornerSeq X a) := by
    rw [← cornerSeq_sub]
    exact (isNull_cornerSeq_iff X cofinite _).mpr hnull
  have hzero : normMatrixCStarCoronaMk (fun n ↦ increasingBlockModel X n)
      (cornerSeq X (coronaLift X (normMatrixCStarCoronaMk (fun n ↦ X n) a))
        - cornerSeq X a) = 0 :=
    (normMatrixCStarCoronaMk_eq_zero_iff _ _).mpr hnull'
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-- **The corner map on coronas, as a nonunital `⋆`-homomorphism.**  It is not
unital, and `HasMFEmbedding` does not ask it to be: the printed definition
allows a nonunital embedding, and no unital algebra map can raise the matrix
size. -/
def cornerCoronaHom :
    NormMatrixCStarCorona (fun n ↦ X n) →⋆ₙₐ[ℂ]
      NormMatrixCStarCorona (fun n ↦ increasingBlockModel X n) where
  toFun := cornerCorona X
  map_smul' c x := by
    obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x
    -- the field's statement carries `MonoidHom.id ℂ` on the right; normalize it
    -- away first, so the closing `rfl` of the rewrite chain is syntactic.
    show cornerCorona X (c • normMatrixCStarCoronaMk (fun n ↦ X n) a)
      = c • cornerCorona X (normMatrixCStarCoronaMk (fun n ↦ X n) a)
    have hsmul : c • normMatrixCStarCoronaMk (fun n ↦ X n) a
        = normMatrixCStarCoronaMk (fun n ↦ X n) (c • a) :=
      (normMatrixCStarCoronaMk_smul (fun n ↦ X n) c a).symm
    rw [hsmul, cornerCorona_mk, cornerCorona_mk, cornerSeq_smul,
      normMatrixCStarCoronaMk_smul]
  map_zero' := by
    have h0 : cornerCorona X (normMatrixCStarCoronaMk (fun n ↦ X n) 0) = 0 := by
      rw [cornerCorona_mk, cornerSeq_zero, map_zero]
    rwa [map_zero] at h0
  map_add' x y := by
    obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x
    obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) y
    have hsum : normMatrixCStarCoronaMk (fun n ↦ X n) a
          + normMatrixCStarCoronaMk (fun n ↦ X n) b
        = normMatrixCStarCoronaMk (fun n ↦ X n) (a + b) :=
      (map_add (normMatrixCStarCoronaMk (fun n ↦ X n)) a b).symm
    rw [hsum, cornerCorona_mk, cornerCorona_mk, cornerCorona_mk,
      cornerSeq_add, map_add]
  map_mul' x y := by
    obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x
    obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) y
    have hprod : normMatrixCStarCoronaMk (fun n ↦ X n) a
          * normMatrixCStarCoronaMk (fun n ↦ X n) b
        = normMatrixCStarCoronaMk (fun n ↦ X n) (a * b) :=
      (map_mul (normMatrixCStarCoronaMk (fun n ↦ X n)) a b).symm
    rw [hprod, cornerCorona_mk, cornerCorona_mk, cornerCorona_mk,
      cornerSeq_mul, map_mul]
  map_star' x := by
    obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x
    rw [normMatrixCStarCorona_star_mk, cornerCorona_mk, cornerCorona_mk,
      cornerSeq_star, normMatrixCStarCorona_star_mk]

@[simp] theorem cornerCoronaHom_apply
    (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    cornerCoronaHom X x = cornerCorona X x := rfl

/-- **The corner map on coronas is injective.**  Directly from
`isNull_cornerSeq_iff`: a difference of lifts is null exactly when its corner
image is. -/
theorem cornerCoronaHom_injective :
    Function.Injective (cornerCoronaHom X) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x
  obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) y
  rw [cornerCoronaHom_apply, cornerCoronaHom_apply, cornerCorona_mk,
    cornerCorona_mk, ← sub_eq_zero, ← map_sub,
    normMatrixCStarCoronaMk_eq_zero_iff, ← cornerSeq_sub] at hxy
  rw [← sub_eq_zero, ← map_sub, normMatrixCStarCoronaMk_eq_zero_iff]
  exact (isNull_cornerSeq_iff X cofinite (a - b)).mp hxy

end

/-! ## The two definitions and their equivalence -/

/-- **The manuscript's MF definition.**  An embedding into the corona over an
arbitrary sequence of positive matrix sizes, with no monotonicity required:

> Given a sequence `(d_n)` of positive integers, write
> `Q((d_n)) = ∏_n M_{d_n}(ℂ) / ⨁_n M_{d_n}(ℂ)` … a separable `C*`-algebra is
> MF if it embeds into an algebra of the form `Q((d_n))`.

`Analysis/MFAlgebra.HasMFEmbedding` is the same statement with `StrictMono` on
the dimensions; the manuscript's convention paragraph asserts the two agree. -/
def HasUnrestrictedMFEmbedding (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  ∃ X : ℕ → FiniteModel, ∃ hne : ∀ n, Nonempty (X n),
    letI : ∀ n, Nonempty (X n) := hne
    (∀ n, 0 < Fintype.card (X n)) ∧
      ∃ e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n),
        Function.Injective e

/-- **The convention paragraph, proved.**  Nothing changes if the dimensions are
required to be strictly increasing: an embedding over an arbitrary positive
dimension sequence composes with the corner map into the cumulative models,
whose dimensions strictly increase. -/
theorem hasMFEmbedding_iff (A : Type u) [NonUnitalCStarAlgebra A] :
    HasMFEmbedding A ↔ HasUnrestrictedMFEmbedding A := by
  constructor
  · rintro ⟨X, hne, hpos, _hmono, e, he⟩
    exact ⟨X, hne, hpos, e, he⟩
  · rintro ⟨X, hne, hpos, e, he⟩
    letI : ∀ n, Nonempty (X n) := hne
    have hinj : Function.Injective ⇑((cornerCoronaHom X).comp e) :=
      fun p q hpq ↦ he (cornerCoronaHom_injective X hpq)
    exact ⟨increasingBlockModel X, nonempty_increasingBlockModel X hne,
      fun n ↦ card_increasingBlockModel_pos X n,
      strictMono_card_increasingBlockModel X hpos,
      (cornerCoronaHom X).comp e, hinj⟩

/-- The literature-standard predicate with the printed, unrestricted dimension
sequence. -/
def IsUnrestrictedMFAlgebra (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  TopologicalSpace.SeparableSpace A ∧ HasUnrestrictedMFEmbedding A

/-- **The Blackadar--Kirchberg definition is insensitive to the dimension
sequence.**  This is the algebra-level counterpart of
`Sofic/OperatorMFIncreasingDimensions.isOperatorMFIncreasing_iff`, which proves
the same normalization for the group predicate. -/
theorem isMFAlgebra_iff (A : Type u) [NonUnitalCStarAlgebra A] :
    IsMFAlgebra A ↔ IsUnrestrictedMFAlgebra A :=
  and_congr_right fun _ ↦ hasMFEmbedding_iff A

end MFAlgebraDimension
end GroupApproximation
