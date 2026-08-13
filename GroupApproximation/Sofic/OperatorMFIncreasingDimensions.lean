import GroupApproximation.Sofic.NormMFUniversalCorona

/-!
# Increasing-dimension normalization for operator-MF groups

Carrión--Dadarlat--Eckhardt formulate the MF target using an increasing
sequence of positive matrix sizes.  `IsOperatorMF` allows an arbitrary
positive sequence, which is convenient for constructions but should not be
silently identified with the printed convention.

This file proves the equivalence.  Replace the ambient type at coordinate `n`
by the cumulative sum `X 0 ⊕ ... ⊕ X n`, but embed only the `n`th model:
put its unitary in the newest block and identities in the other blocks.  Thus
no earlier approximation error is carried into later coordinates.  Operator
norm distance from the identity is unchanged, so the map preserves and
reflects the cofinite null subgroup.  It therefore induces an injective
homomorphism of unitary-sequence coronas, while positivity of the ambient
summands makes their dimensions strictly increase.

This normalization concerns matrix sizes only.  The polar-correction
identification with the unitary group of the C-star-algebra quotient is proved
separately in `Analysis.NormMatrixCoronaUnitary` and combined with this result
in `Sofic.CDEOperatorMF`.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-- The cumulative block model `X 0 ⊕ ... ⊕ X n`. -/
def increasingBlockModel (X : ℕ → FiniteModel) : ℕ → FiniteModel
  | 0 => X 0
  | n + 1 => blockSumModel (increasingBlockModel X n) (X (n + 1))

@[simp] theorem card_increasingBlockModel_zero (X : ℕ → FiniteModel) :
    Fintype.card (increasingBlockModel X 0) = Fintype.card (X 0) :=
  rfl

@[simp] theorem card_increasingBlockModel_succ
    (X : ℕ → FiniteModel) (n : ℕ) :
    Fintype.card (increasingBlockModel X (n + 1)) =
      Fintype.card (increasingBlockModel X n) + Fintype.card (X (n + 1)) := by
  change Fintype.card
      ((increasingBlockModel X n : Type) ⊕ (X (n + 1) : Type)) = _
  exact Fintype.card_sum

/-- Positive input dimensions make the cumulative dimensions strictly
increase at every successor step. -/
theorem card_increasingBlockModel_lt_succ
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) (n : ℕ) :
    Fintype.card (increasingBlockModel X n) <
      Fintype.card (increasingBlockModel X (n + 1)) := by
  rw [card_increasingBlockModel_succ]
  have hpos := hX (n + 1)
  omega

theorem strictMono_card_increasingBlockModel
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    StrictMono (fun n => Fintype.card (increasingBlockModel X n)) :=
  strictMono_nat_of_lt_succ (card_increasingBlockModel_lt_succ X hX)

/-- Embed the `n`th old unitary group in the newest block of the cumulative
model, using the identity on all earlier blocks. -/
def increasingCoordinateEmbed (X : ℕ → FiniteModel) :
    ∀ n, Matrix.unitaryGroup (X n) ℂ →*
      Matrix.unitaryGroup (increasingBlockModel X n) ℂ
  | 0 => MonoidHom.id _
  | n + 1 =>
      { toFun := fun u =>
          ⟨blockDiagMatrix (increasingBlockModel X n) (X (n + 1)) 1 u,
            blockDiagMatrix_mem_unitaryGroup
              (increasingBlockModel X n) (X (n + 1))
              (one_mem _) u.property⟩
        map_one' := by
          apply Subtype.ext
          exact blockDiagMatrix_one _ _
        map_mul' := by
          intro a b
          apply Subtype.ext
          change
            blockDiagMatrix (increasingBlockModel X n) (X (n + 1)) 1
                ((a : Matrix (X (n + 1)) (X (n + 1)) ℂ) * b) =
              blockDiagMatrix (increasingBlockModel X n) (X (n + 1)) 1 a *
                blockDiagMatrix (increasingBlockModel X n) (X (n + 1)) 1 b
          rw [blockDiagMatrix_mul, one_mul] }

/-- The cumulative block embedding preserves distance from the identity
exactly, coordinate by coordinate. -/
theorem opLength_increasingCoordinateEmbed
    (X : ℕ → FiniteModel) (n : ℕ)
    (u : Matrix.unitaryGroup (X n) ℂ) :
    opLength (increasingBlockModel X n) (increasingCoordinateEmbed X n u) =
      opLength (X n) u := by
  cases n with
  | zero => rfl
  | succ n =>
      unfold opLength
      change
        ‖blockDiagMatrix (increasingBlockModel X n) (X (n + 1)) 1 u - 1‖ =
          ‖(u : Matrix (X (n + 1)) (X (n + 1)) ℂ) - 1‖
      rw [← blockDiagMatrix_one, blockDiagMatrix_sub, l2_opNorm_blockDiag]
      rw [sub_self, norm_zero, max_eq_right (norm_nonneg _)]

/-- Coordinatewise cumulative block embedding of unitary sequences. -/
def increasingSequenceEmbed (X : ℕ → FiniteModel) :
    (∀ n, Matrix.unitaryGroup (X n) ℂ) →*
      ∀ n, Matrix.unitaryGroup (increasingBlockModel X n) ℂ where
  toFun v n := increasingCoordinateEmbed X n (v n)
  map_one' := by
    funext n
    exact map_one (increasingCoordinateEmbed X n)
  map_mul' v w := by
    funext n
    exact map_mul (increasingCoordinateEmbed X n) (v n) (w n)

@[simp] theorem increasingSequenceEmbed_apply
    (X : ℕ → FiniteModel)
    (v : ∀ n, Matrix.unitaryGroup (X n) ℂ) (n : ℕ) :
    increasingSequenceEmbed X v n = increasingCoordinateEmbed X n (v n) :=
  rfl

/-- The sequence embedding preserves and reflects convergence to the
identity along the cofinite filter. -/
theorem isNullCofiniteOpSeq_increasingSequenceEmbed_iff
    (X : ℕ → FiniteModel)
    (v : ∀ n, Matrix.unitaryGroup (X n) ℂ) :
    IsNullCofiniteOpSeq (increasingBlockModel X) (increasingSequenceEmbed X v) ↔
      IsNullCofiniteOpSeq X v := by
  simp only [IsNullCofiniteOpSeq, increasingSequenceEmbed_apply,
    opLength_increasingCoordinateEmbed]

/-- The pre-quotient homomorphism into the cumulative block corona. -/
def increasingCoronaPreHom (X : ℕ → FiniteModel) :
    (∀ n, Matrix.unitaryGroup (X n) ℂ) →*
      NormMatrixCoronaUnitary (increasingBlockModel X) :=
  (QuotientGroup.mk' (nullCofiniteOpSubgroup (increasingBlockModel X))).comp
    (increasingSequenceEmbed X)

theorem ker_increasingCoronaPreHom (X : ℕ → FiniteModel) :
    (increasingCoronaPreHom X).ker = nullCofiniteOpSubgroup X := by
  ext v
  change increasingCoronaPreHom X v = 1 ↔ IsNullCofiniteOpSeq X v
  rw [increasingCoronaPreHom, MonoidHom.comp_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact isNullCofiniteOpSeq_increasingSequenceEmbed_iff X v

/-- Faithful homomorphism from an arbitrary positive-dimension
unitary-sequence corona to one whose dimensions strictly increase. -/
def increasingCoronaEmbed (X : ℕ → FiniteModel) :
    NormMatrixCoronaUnitary X →*
      NormMatrixCoronaUnitary (increasingBlockModel X) :=
  QuotientGroup.lift (nullCofiniteOpSubgroup X) (increasingCoronaPreHom X) (by
    rw [ker_increasingCoronaPreHom])

theorem increasingCoronaEmbed_injective (X : ℕ → FiniteModel) :
    Function.Injective (increasingCoronaEmbed X) := by
  apply (QuotientGroup.injective_lift_iff
    (N := nullCofiniteOpSubgroup X) (increasingCoronaPreHom X) (by
      rw [ker_increasingCoronaPreHom])).2
  exact (ker_increasingCoronaPreHom X).symm

/-- The CDE dimension convention: a faithful unitary-sequence-corona
representation with positive, strictly increasing matrix sizes. -/
def IsOperatorMFIncreasing (G : Type u) [Group G] : Prop :=
  ∃ X : ℕ → FiniteModel,
    (∀ n, 0 < Fintype.card (X n)) ∧
      StrictMono (fun n => Fintype.card (X n)) ∧
        ∃ rho : G →* NormMatrixCoronaUnitary X, Function.Injective rho

/-- Arbitrary positive dimensions and strictly increasing positive dimensions
define the same operator-MF property. -/
theorem isOperatorMFIncreasing_iff :
    IsOperatorMFIncreasing G ↔ IsOperatorMF G := by
  constructor
  · rintro ⟨X, hX, _hmono, rho, hrho⟩
    exact ⟨X, hX, rho, hrho⟩
  · rintro ⟨X, hX, rho, hrho⟩
    refine ⟨increasingBlockModel X, ?_,
      strictMono_card_increasingBlockModel X hX,
      (increasingCoronaEmbed X).comp rho,
      (increasingCoronaEmbed_injective X).comp hrho⟩
    intro n
    cases n with
    | zero => exact hX 0
    | succ n =>
        rw [card_increasingBlockModel_succ]
        have hpos := hX (n + 1)
        omega

end GroupApproximation
