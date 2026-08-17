import GroupApproximation.Sofic.ScaledKazhdanTransport
import GroupApproximation.Sofic.NormMFUniversalCorona
import GroupApproximation.Sofic.ManuscriptKazhdanTransport

/-!
# Kazhdan transport of asymptotic intertwiners

The transport theorem of `Sofic.KazhdanAsymptoticCommutant` moves the
Hilbert--Schmidt asymptotic commutant of a Kazhdan image — the fixed
tensors of the adjoint sector — through a one-sided compressor.  This file
proves the transport at every tensor type: for ANY two operator-norm
almost representations `B₁, B₂` of the ambient group, the compressor
carries uniformly bounded block-normalized asymptotic intertwiners between
`B₁|Γ` and `B₂|Γ` to asymptotic intertwiners, and likewise at every
nonnegative weight in the sense of `Sofic.ScaledKazhdanTransport`.

The proof is a reduction, not a new estimate: a rectangular intertwiner is
the off-diagonal corner of a Hilbert--Schmidt asymptotic commutant of the
block-diagonal almost representation `B₁ ⊕ B₂`, which is again an
operator-norm almost representation because block sums have operator norm
`max` and tensor structure plays no role.  Applying the established
transport to the block sum and reading off the corner gives the theorem.
Fixed tensors of type `(p, q)` are the instance `B₁ = U^{⊗p}`,
`B₂ = U^{⊗q}`: compression creates no asymptotic invariant vectors,
forms, or intertwiners of any fixed type, at any scale.
-/

namespace GroupApproximation
namespace IntertwinerKazhdanTransport

open Matrix KazhdanCornerMatrices KazhdanAsymptoticCommutant
open ScaledKazhdanTransport
open scoped Matrix.Norms.L2Operator

universe u v

/-! The ambient group carrying the two almost representations is quantified at
an arbitrary universe, as in the manuscript.  The Kazhdan source `Γ` is fixed at
`Type 0` for the *theorems* of this file, which is where the transport proof
lives; the **predicates** carry their own universe binder instead of taking it
from here, so that the printed generality can be stated.  What closes the gap is
not a sweep of these proofs but the derived-countability descent of
`Sofic.TransportVariantsAnyUniverse`: property `(T)` forces a finite generating
set, so a Kazhdan source in any universe has a `Type 0` model and the datum
travels to it. -/
variable {Γ : Type} {E : Type u} [Group Γ] [Group E]

/-! ## Rectangular mass and the off-diagonal block embedding -/

/-- Unnormalized squared Frobenius mass of a rectangular matrix. -/
noncomputable def rectMass {Y Z : FiniteModel} (X : Matrix Y Z ℂ) : ℝ :=
  ∑ i : Y, ∑ j : Z, Complex.normSq (X i j)

theorem rectMass_nonneg {Y Z : FiniteModel} (X : Matrix Y Z ℂ) :
    0 ≤ rectMass X :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
    Complex.normSq_nonneg _

/-- The strictly upper off-diagonal embedding of a rectangular matrix into
the block-sum model. -/
def offDiagBlock (Y Z : FiniteModel) (X : Matrix Y Z ℂ) :
    Matrix (blockSumModel Y Z) (blockSumModel Y Z) ℂ :=
  Matrix.fromBlocks 0 X 0 0

theorem offDiagBlock_sub (Y Z : FiniteModel) (X X' : Matrix Y Z ℂ) :
    offDiagBlock Y Z X - offDiagBlock Y Z X' =
      offDiagBlock Y Z (X - X') := by
  ext p q
  cases p <;> cases q <;>
    simp [offDiagBlock, Matrix.fromBlocks, Matrix.sub_apply]

theorem blockDiag_mul_offDiag (Y Z : FiniteModel) (A : Matrix Y Y ℂ)
    (B : Matrix Z Z ℂ) (X : Matrix Y Z ℂ) :
    blockDiagMatrix Y Z A B * offDiagBlock Y Z X =
      offDiagBlock Y Z (A * X) := by
  unfold blockDiagMatrix offDiagBlock
  rw [Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem offDiag_mul_blockDiag (Y Z : FiniteModel) (X : Matrix Y Z ℂ)
    (A : Matrix Y Y ℂ) (B : Matrix Z Z ℂ) :
    offDiagBlock Y Z X * blockDiagMatrix Y Z A B =
      offDiagBlock Y Z (X * B) := by
  unfold blockDiagMatrix offDiagBlock
  rw [Matrix.fromBlocks_multiply]
  congr 1 <;> simp

/-- Conjugating the embedded corner by a block-diagonal pair acts by the
two-sided intertwining action on the corner. -/
theorem blockDiag_conj_offDiag (Y Z : FiniteModel) (U : Matrix Y Y ℂ)
    (V : Matrix Z Z ℂ) (X : Matrix Y Z ℂ) :
    blockDiagMatrix Y Z U V * offDiagBlock Y Z X *
        (blockDiagMatrix Y Z U V)ᴴ =
      offDiagBlock Y Z (U * X * Vᴴ) := by
  rw [blockDiagMatrix_conjTranspose, blockDiag_mul_offDiag,
    offDiag_mul_blockDiag]

theorem blockDiag_star_conj_offDiag (Y Z : FiniteModel) (U : Matrix Y Y ℂ)
    (V : Matrix Z Z ℂ) (X : Matrix Y Z ℂ) :
    (blockDiagMatrix Y Z U V)ᴴ * offDiagBlock Y Z X *
        blockDiagMatrix Y Z U V =
      offDiagBlock Y Z (Uᴴ * X * V) := by
  rw [blockDiagMatrix_conjTranspose, blockDiag_mul_offDiag,
    offDiag_mul_blockDiag]

/-- The Frobenius mass of the embedded corner is the rectangular mass. -/
theorem sum_normSq_offDiagBlock (Y Z : FiniteModel) (X : Matrix Y Z ℂ) :
    (∑ p : Y ⊕ Z, ∑ q : Y ⊕ Z,
        Complex.normSq (offDiagBlock Y Z X p q)) = rectMass X := by
  rw [Fintype.sum_sum_type]
  have h₁ : ∀ i : Y, (∑ q : Y ⊕ Z,
      Complex.normSq (offDiagBlock Y Z X (Sum.inl i) q)) =
      ∑ j : Z, Complex.normSq (X i j) := by
    intro i
    rw [Fintype.sum_sum_type]
    simp [offDiagBlock]
  have h₂ : ∀ i : Z, (∑ q : Y ⊕ Z,
      Complex.normSq (offDiagBlock Y Z X (Sum.inr i) q)) = 0 := by
    intro i
    rw [Fintype.sum_sum_type]
    simp [offDiagBlock]
  rw [Finset.sum_congr rfl fun i _ ↦ h₁ i,
    Finset.sum_congr rfl fun i _ ↦ h₂ i]
  simp [rectMass]

theorem matMass_offDiagBlock (Y Z : FiniteModel) (X : Matrix Y Z ℂ) :
    matMass (offDiagBlock Y Z X) = rectMass X := by
  show (∑ p : Y ⊕ Z, ∑ q : Y ⊕ Z,
      Complex.normSq (offDiagBlock Y Z X p q)) = rectMass X
  exact sum_normSq_offDiagBlock Y Z X

theorem hsNormSq_offDiagBlock (Y Z : FiniteModel) (X : Matrix Y Z ℂ) :
    hsNormSq (blockSumModel Y Z) (offDiagBlock Y Z X) =
      rectMass X / ((Fintype.card Y : ℝ) + Fintype.card Z) := by
  have hcard : ((Fintype.card (blockSumModel Y Z) : ℕ) : ℝ) =
      (Fintype.card Y : ℝ) + Fintype.card Z := by
    have h : Fintype.card (blockSumModel Y Z) =
        Fintype.card Y + Fintype.card Z := Fintype.card_sum
    rw [h]
    push_cast
    ring
  show (∑ p : Y ⊕ Z, ∑ q : Y ⊕ Z,
      Complex.normSq (offDiagBlock Y Z X p q)) /
      ((Fintype.card (blockSumModel Y Z) : ℕ) : ℝ) = _
  rw [sum_normSq_offDiagBlock, hcard]

/-- Rectangular matrix-vector products are controlled by the rectangular
operator norm. -/
theorem rect_sum_normSq_mulVec_le {R S : Type*} [Fintype R] [Fintype S]
    [DecidableEq S] (C : Matrix R S ℂ) (x : S → ℂ) :
    ∑ i : R, Complex.normSq ((C *ᵥ x) i) ≤
      ‖C‖ ^ 2 * ∑ j : S, Complex.normSq (x j) := by
  have h : ‖(EuclideanSpace.equiv R ℂ).symm (C *ᵥ x)‖ ≤
      ‖C‖ * ‖(EuclideanSpace.equiv S ℂ).symm x‖ :=
    Matrix.l2_opNorm_mulVec C ((EuclideanSpace.equiv S ℂ).symm x)
  have hL := euclidean_norm_sq_general (C *ᵥ x)
  have hR := euclidean_norm_sq_general x
  have hsquare : ‖(EuclideanSpace.equiv R ℂ).symm (C *ᵥ x)‖ ^ 2 ≤
      (‖C‖ * ‖(EuclideanSpace.equiv S ℂ).symm x‖) ^ 2 := by
    nlinarith [norm_nonneg ((EuclideanSpace.equiv R ℂ).symm (C *ᵥ x)),
      norm_nonneg C, norm_nonneg ((EuclideanSpace.equiv S ℂ).symm x)]
  calc
    ∑ i : R, Complex.normSq ((C *ᵥ x) i) =
        ‖(EuclideanSpace.equiv R ℂ).symm (C *ᵥ x)‖ ^ 2 := hL.symm
    _ ≤ (‖C‖ * ‖(EuclideanSpace.equiv S ℂ).symm x‖) ^ 2 := hsquare
    _ = ‖C‖ ^ 2 * ∑ j : S, Complex.normSq (x j) := by
      rw [mul_pow, hR]

/-- Embedding a rectangular matrix as an off-diagonal corner does not
increase the operator norm. -/
theorem l2_opNorm_offDiagBlock_le (Y Z : FiniteModel) (X : Matrix Y Z ℂ) :
    ‖offDiagBlock Y Z X‖ ≤ ‖X‖ := by
  classical
  refine l2_opNorm_le_of_sum_normSq_general (offDiagBlock Y Z X)
    (norm_nonneg X) fun v ↦ ?_
  have hmv : (offDiagBlock Y Z X) *ᵥ v =
      Sum.elim (X *ᵥ (v ∘ Sum.inr)) 0 := by
    unfold offDiagBlock
    rw [Matrix.fromBlocks_mulVec]
    congr 1 <;> simp
  calc
    (∑ p : Y ⊕ Z,
        Complex.normSq (((offDiagBlock Y Z X) *ᵥ v) p)) =
        (∑ i : Y,
          Complex.normSq (((offDiagBlock Y Z X) *ᵥ v) (Sum.inl i))) +
          ∑ j : Z,
            Complex.normSq (((offDiagBlock Y Z X) *ᵥ v) (Sum.inr j)) :=
      Fintype.sum_sum_type _
    _ = ∑ i : Y, Complex.normSq ((X *ᵥ (v ∘ Sum.inr)) i) := by
      rw [hmv]
      simp
    _ ≤ ‖X‖ ^ 2 * ∑ j : Z, Complex.normSq ((v ∘ Sum.inr) j) :=
      rect_sum_normSq_mulVec_le X _
    _ ≤ ‖X‖ ^ 2 * ∑ p : Y ⊕ Z, Complex.normSq (v p) := by
      have hle : (∑ j : Z, Complex.normSq ((v ∘ Sum.inr) j)) ≤
          ∑ p : Y ⊕ Z, Complex.normSq (v p) := by
        rw [Fintype.sum_sum_type]
        exact le_add_of_nonneg_left
          (Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _)
      have hX2 : (0 : ℝ) ≤ ‖X‖ ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_left hle hX2

/-! ## The block-sum almost representation -/

/-- The block-diagonal direct sum of two operator-norm almost
representations. -/
@[reducible] def blockSumRep (B₁ B₂ : OpAlmostRepresentation E) :
    OpAlmostRepresentation E where
  model n := blockSumModel (B₁.model n) (B₂.model n)
  modelNonempty n := by
    have h₁ := B₁.modelNonempty n
    have hcard : Fintype.card (blockSumModel (B₁.model n) (B₂.model n)) =
        Fintype.card (B₁.model n) + Fintype.card (B₂.model n) :=
      Fintype.card_sum
    omega
  map n g := ⟨blockDiagMatrix (B₁.model n) (B₂.model n)
      (B₁.map n g) (B₂.map n g),
    blockDiagMatrix_mem_unitaryGroup _ _ (B₁.map n g).2 (B₂.map n g).2⟩
  asymptoticallyMultiplicative g h ε hε := by
    obtain ⟨N₁, hN₁⟩ := B₁.asymptoticallyMultiplicative g h ε hε
    obtain ⟨N₂, hN₂⟩ := B₂.asymptoticallyMultiplicative g h ε hε
    refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
    show ‖blockDiagMatrix (B₁.model n) (B₂.model n)
        (B₁.map n (g * h)) (B₂.map n (g * h)) -
        blockDiagMatrix (B₁.model n) (B₂.model n)
            (B₁.map n g) (B₂.map n g) *
          blockDiagMatrix (B₁.model n) (B₂.model n)
            (B₁.map n h) (B₂.map n h)‖ ≤ ε
    rw [blockDiagMatrix_mul, blockDiagMatrix_sub, l2_opNorm_blockDiag]
    exact max_le (hN₁ n ((le_max_left _ _).trans hn))
      (hN₂ n ((le_max_right _ _).trans hn))

@[simp] theorem blockSumRep_map_coe (B₁ B₂ : OpAlmostRepresentation E)
    (n : ℕ) (g : E) :
    ((blockSumRep B₁ B₂).map n g :
        Matrix ((blockSumRep B₁ B₂).model n)
          ((blockSumRep B₁ B₂).model n) ℂ) =
      blockDiagMatrix (B₁.model n) (B₂.model n)
        (B₁.map n g) (B₂.map n g) := rfl

theorem blockCard_pos (B₁ B₂ : OpAlmostRepresentation E) (n : ℕ) :
    (0 : ℝ) < (Fintype.card (B₁.model n) : ℝ) +
      Fintype.card (B₂.model n) := by
  have h : 0 < Fintype.card (B₁.model n) + Fintype.card (B₂.model n) :=
    Nat.add_pos_left (B₁.modelNonempty n) _
  exact_mod_cast h

/-! ## Asymptotic intertwiners -/

/-- A rectangular sequence asymptotically intertwines the
`iota`-restrictions of two almost representations, in the block-normalized
Hilbert--Schmidt sense. -/
def IsAsymptoticIntertwinerOf (B₁ B₂ : OpAlmostRepresentation E)
    (iota : Γ →* E)
    (x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ) : Prop :=
  ∀ γ : Γ, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
    rectMass (x n -
        (B₁.map n (iota γ) :
          Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
          (B₂.map n (iota γ) :
            Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ) ≤
      ε * ((Fintype.card (B₁.model n) : ℝ) + Fintype.card (B₂.model n))

/-- The compression-core form of the asymptotic intertwiner. -/
abbrev IsAsymptoticIntertwiner (B₁ B₂ : OpAlmostRepresentation E)
    (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ) : Prop :=
  IsAsymptoticIntertwinerOf B₁ B₂ C.iota x

/-- Uniform operator-norm boundedness of a rectangular sequence. -/
def IsUniformlyBoundedRect (B₁ B₂ : OpAlmostRepresentation E)
    (x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M

theorem isUniformlyBoundedRect_zero (B₁ B₂ : OpAlmostRepresentation E) :
    IsUniformlyBoundedRect B₁ B₂ (fun _ ↦ 0) := by
  refine ⟨0, le_refl 0, fun n ↦ ?_⟩
  simp

/-- Intertwiners are exactly the off-diagonal Hilbert--Schmidt asymptotic
commutants of the block sum. -/
theorem isAsymptoticCommutantOf_offDiag_iff
    (B₁ B₂ : OpAlmostRepresentation E) (iota : Γ →* E)
    (x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ) :
    IsAsymptoticCommutantOf (blockSumRep B₁ B₂) iota
        (fun n ↦ offDiagBlock (B₁.model n) (B₂.model n) (x n)) ↔
      IsAsymptoticIntertwinerOf B₁ B₂ iota x := by
  constructor
  · intro h γ ε hε
    obtain ⟨N, hN⟩ := h γ ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have hval : hsNormSq (blockSumModel (B₁.model n) (B₂.model n))
        (offDiagBlock (B₁.model n) (B₂.model n) (x n) -
          blockDiagMatrix (B₁.model n) (B₂.model n)
              (B₁.map n (iota γ)) (B₂.map n (iota γ)) *
            offDiagBlock (B₁.model n) (B₂.model n) (x n) *
            (blockDiagMatrix (B₁.model n) (B₂.model n)
              (B₁.map n (iota γ)) (B₂.map n (iota γ)))ᴴ) ≤ ε := hN n hn
    rw [blockDiag_conj_offDiag, offDiagBlock_sub,
      hsNormSq_offDiagBlock] at hval
    exact (div_le_iff₀ (blockCard_pos B₁ B₂ n)).mp hval
  · intro h γ ε hε
    obtain ⟨N, hN⟩ := h γ ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    show hsNormSq (blockSumModel (B₁.model n) (B₂.model n))
        (offDiagBlock (B₁.model n) (B₂.model n) (x n) -
          blockDiagMatrix (B₁.model n) (B₂.model n)
              (B₁.map n (iota γ)) (B₂.map n (iota γ)) *
            offDiagBlock (B₁.model n) (B₂.model n) (x n) *
            (blockDiagMatrix (B₁.model n) (B₂.model n)
              (B₁.map n (iota γ)) (B₂.map n (iota γ)))ᴴ) ≤ ε
    rw [blockDiag_conj_offDiag, offDiagBlock_sub, hsNormSq_offDiagBlock]
    exact (div_le_iff₀ (blockCard_pos B₁ B₂ n)).mpr (hN n hn)

theorem isUniformlyBounded_offDiag (B₁ B₂ : OpAlmostRepresentation E)
    {x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ}
    (hx : IsUniformlyBoundedRect B₁ B₂ x) :
    IsUniformlyBounded (blockSumRep B₁ B₂)
      (fun n ↦ offDiagBlock (B₁.model n) (B₂.model n) (x n)) := by
  obtain ⟨M, hM, hMx⟩ := hx
  exact ⟨M, hM, fun n ↦ (l2_opNorm_offDiagBlock_le _ _ _).trans (hMx n)⟩

/-! ## The transport theorems -/

/-- **Kazhdan transport of asymptotic intertwiners.**  A one-sided
compressor of a Kazhdan image carries every uniformly bounded
block-normalized Hilbert--Schmidt asymptotic intertwiner between two
operator-norm almost representations of the ambient group to another
one. -/
theorem intertwiner_transport (B₁ B₂ : OpAlmostRepresentation E)
    (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ)
    (hx : IsAsymptoticIntertwiner B₁ B₂ C x)
    (hbound : IsUniformlyBoundedRect B₁ B₂ x) :
    IsAsymptoticIntertwiner B₁ B₂ C (fun n ↦
      (B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
        (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ) := by
  have hcomm := (isAsymptoticCommutantOf_offDiag_iff B₁ B₂ C.iota x).mpr hx
  have htrans := transport (blockSumRep B₁ B₂) C
    (fun n ↦ offDiagBlock (B₁.model n) (B₂.model n) (x n)) hcomm
    (isUniformlyBounded_offDiag B₁ B₂ hbound)
  have hz : ∀ n : ℕ,
      ((blockSumRep B₁ B₂).map n C.t :
          Matrix (blockSumModel (B₁.model n) (B₂.model n))
            (blockSumModel (B₁.model n) (B₂.model n)) ℂ) *
          offDiagBlock (B₁.model n) (B₂.model n) (x n) *
          ((blockSumRep B₁ B₂).map n C.t :
            Matrix (blockSumModel (B₁.model n) (B₂.model n))
              (blockSumModel (B₁.model n) (B₂.model n)) ℂ)ᴴ =
        offDiagBlock (B₁.model n) (B₂.model n)
          ((B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
            (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ) := by
    intro n
    rw [blockSumRep_map_coe, blockDiag_conj_offDiag]
  have hcomm' : IsAsymptoticCommutantOf (blockSumRep B₁ B₂) C.iota
      (fun n ↦ offDiagBlock (B₁.model n) (B₂.model n)
        ((B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
          (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ)) := by
    intro γ
    exact (htrans γ).congr fun n ↦ by simp only [hz]
  exact (isAsymptoticCommutantOf_offDiag_iff B₁ B₂ C.iota _).mp hcomm'

/-- **Reverse transport.**  The adjoint compressor acts in the opposite
direction on asymptotic intertwiners. -/
theorem intertwiner_transport_star (B₁ B₂ : OpAlmostRepresentation E)
    (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ)
    (hx : IsAsymptoticIntertwiner B₁ B₂ C x)
    (hbound : IsUniformlyBoundedRect B₁ B₂ x) :
    IsAsymptoticIntertwiner B₁ B₂ C (fun n ↦
      (B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ)ᴴ * x n *
        (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)) := by
  have hcomm := (isAsymptoticCommutantOf_offDiag_iff B₁ B₂ C.iota x).mpr hx
  have htrans := transport_star (blockSumRep B₁ B₂) C
    (fun n ↦ offDiagBlock (B₁.model n) (B₂.model n) (x n)) hcomm
    (isUniformlyBounded_offDiag B₁ B₂ hbound)
  have hz : ∀ n : ℕ,
      ((blockSumRep B₁ B₂).map n C.t :
          Matrix (blockSumModel (B₁.model n) (B₂.model n))
            (blockSumModel (B₁.model n) (B₂.model n)) ℂ)ᴴ *
          offDiagBlock (B₁.model n) (B₂.model n) (x n) *
          ((blockSumRep B₁ B₂).map n C.t :
            Matrix (blockSumModel (B₁.model n) (B₂.model n))
              (blockSumModel (B₁.model n) (B₂.model n)) ℂ) =
        offDiagBlock (B₁.model n) (B₂.model n)
          ((B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ)ᴴ * x n *
            (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)) := by
    intro n
    rw [blockSumRep_map_coe, blockDiag_star_conj_offDiag]
  have hcomm' : IsAsymptoticCommutantOf (blockSumRep B₁ B₂) C.iota
      (fun n ↦ offDiagBlock (B₁.model n) (B₂.model n)
        ((B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ)ᴴ * x n *
          (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ))) := by
    intro γ
    exact (htrans γ).congr fun n ↦ by simp only [hz]
  exact (isAsymptoticCommutantOf_offDiag_iff B₁ B₂ C.iota _).mp hcomm'

/-! ## The scaled versions -/

/-- Scaled asymptotic intertwining at an arbitrary weight.

The source group carries its own universe binder rather than taking `Γ` from the
section, matching `ScaledKazhdanTransport.IsScaledAsymptoticCommutantOf`: the
printed statement quantifies over groups, so the *predicate* must be able to
speak about a source in any universe even where the transport proof below is
carried out at `Type 0`.  Every existing use instantiates `v := 0` and is
unaffected. -/
def IsScaledAsymptoticIntertwinerOf {G : Type v} [Group G]
    (B₁ B₂ : OpAlmostRepresentation E)
    (w : ℕ → ℝ) (iota : G →* E)
    (x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ) : Prop :=
  ∀ γ : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
    rectMass (x n -
        (B₁.map n (iota γ) :
          Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
          (B₂.map n (iota γ) :
            Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ) ≤ ε * w n

/-- Scaled rectangular mass boundedness. -/
def IsScaledRectMassBounded (B₁ B₂ : OpAlmostRepresentation E)
    (w : ℕ → ℝ) (x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ) : Prop :=
  ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ n, rectMass (x n) ≤ Cm * w n

theorem isScaledRectMassBounded_zero (B₁ B₂ : OpAlmostRepresentation E)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    IsScaledRectMassBounded B₁ B₂ w (fun _ ↦ 0) := by
  refine ⟨1, zero_le_one, fun n ↦ ?_⟩
  have h : rectMass (0 : Matrix (B₁.model n) (B₂.model n) ℂ) = 0 := by
    simp [rectMass]
  rw [h, one_mul]
  exact hw n

theorem isScaledAsymptoticCommutantOf_offDiag_iff
    (B₁ B₂ : OpAlmostRepresentation E) (w : ℕ → ℝ) (iota : Γ →* E)
    (x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ) :
    IsScaledAsymptoticCommutantOf (blockSumRep B₁ B₂) w iota
        (fun n ↦ offDiagBlock (B₁.model n) (B₂.model n) (x n)) ↔
      IsScaledAsymptoticIntertwinerOf B₁ B₂ w iota x := by
  constructor
  · intro h γ ε hε
    obtain ⟨N, hN⟩ := h γ ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have hval : matMass
        (offDiagBlock (B₁.model n) (B₂.model n) (x n) -
          blockDiagMatrix (B₁.model n) (B₂.model n)
              (B₁.map n (iota γ)) (B₂.map n (iota γ)) *
            offDiagBlock (B₁.model n) (B₂.model n) (x n) *
            (blockDiagMatrix (B₁.model n) (B₂.model n)
              (B₁.map n (iota γ)) (B₂.map n (iota γ)))ᴴ) ≤ ε * w n :=
      hN n hn
    rw [blockDiag_conj_offDiag, offDiagBlock_sub,
      matMass_offDiagBlock] at hval
    exact hval
  · intro h γ ε hε
    obtain ⟨N, hN⟩ := h γ ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    show matMass
        (offDiagBlock (B₁.model n) (B₂.model n) (x n) -
          blockDiagMatrix (B₁.model n) (B₂.model n)
              (B₁.map n (iota γ)) (B₂.map n (iota γ)) *
            offDiagBlock (B₁.model n) (B₂.model n) (x n) *
            (blockDiagMatrix (B₁.model n) (B₂.model n)
              (B₁.map n (iota γ)) (B₂.map n (iota γ)))ᴴ) ≤ ε * w n
    rw [blockDiag_conj_offDiag, offDiagBlock_sub, matMass_offDiagBlock]
    exact hN n hn

theorem isScaledMassBounded_offDiag (B₁ B₂ : OpAlmostRepresentation E)
    (w : ℕ → ℝ) {x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ}
    (hx : IsScaledRectMassBounded B₁ B₂ w x) :
    IsScaledMassBounded (blockSumRep B₁ B₂) w
      (fun n ↦ offDiagBlock (B₁.model n) (B₂.model n) (x n)) := by
  obtain ⟨Cm, hCm, hCx⟩ := hx
  refine ⟨Cm, hCm, fun n ↦ ?_⟩
  show matMass (offDiagBlock (B₁.model n) (B₂.model n) (x n)) ≤ Cm * w n
  rw [matMass_offDiagBlock]
  exact hCx n

/-- **Scaled Kazhdan transport of asymptotic intertwiners.**  The
transport of intertwiners holds at every nonnegative weight: the block
reduction is weight-blind. -/
theorem scaled_intertwiner_transport :
    ∀ {Γ : Type} {E : Type u} [Group Γ] [Group E]
      (B₁ B₂ : OpAlmostRepresentation E)
      (w : ℕ → ℝ) (_hw : ∀ n, 0 ≤ w n) (C : KazhdanCompressionCore Γ E)
      (x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ)
      (_hx : IsScaledAsymptoticIntertwinerOf B₁ B₂ w C.iota x)
      (_hbound : IsScaledRectMassBounded B₁ B₂ w x),
      IsScaledAsymptoticIntertwinerOf B₁ B₂ w C.iota (fun n ↦
        (B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
          (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ) := by
  intro Γ E _ _ B₁ B₂ w hw C x hx hbound
  have hcomm :=
    (isScaledAsymptoticCommutantOf_offDiag_iff B₁ B₂ w C.iota x).mpr hx
  have htrans := scaled_transport (blockSumRep B₁ B₂) w hw C
    (fun n ↦ offDiagBlock (B₁.model n) (B₂.model n) (x n)) hcomm
    (isScaledMassBounded_offDiag B₁ B₂ w hbound)
  have hz : ∀ n : ℕ,
      ((blockSumRep B₁ B₂).map n C.t :
          Matrix (blockSumModel (B₁.model n) (B₂.model n))
            (blockSumModel (B₁.model n) (B₂.model n)) ℂ) *
          offDiagBlock (B₁.model n) (B₂.model n) (x n) *
          ((blockSumRep B₁ B₂).map n C.t :
            Matrix (blockSumModel (B₁.model n) (B₂.model n))
              (blockSumModel (B₁.model n) (B₂.model n)) ℂ)ᴴ =
        offDiagBlock (B₁.model n) (B₂.model n)
          ((B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
            (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ) := by
    intro n
    rw [blockSumRep_map_coe, blockDiag_conj_offDiag]
  have hcomm' : IsScaledAsymptoticCommutantOf (blockSumRep B₁ B₂) w C.iota
      (fun n ↦ offDiagBlock (B₁.model n) (B₂.model n)
        ((B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
          (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ)) := by
    intro γ
    exact (htrans γ).congr fun n ↦ by simp only [hz]
  exact
    (isScaledAsymptoticCommutantOf_offDiag_iff B₁ B₂ w C.iota _).mp hcomm'

/-! ## The exact manuscript form -/

universe uK

/-- Block-normalized Hilbert--Schmidt vanishing of the rectangular
invariance defect, in natural coordinates. -/
def NaturalHSIntertwinerVanishing {H : Type*} [Group H] (d₁ d₂ : ℕ → ℕ)
    (U₁ : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d₁ n)) ℂ)
    (U₂ : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d₂ n)) ℂ)
    (x : ∀ n, Matrix (naturalFiniteModel (d₁ n))
      (naturalFiniteModel (d₂ n)) ℂ) (g : H) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
    Real.sqrt (rectMass (x n -
        (U₁ n g : Matrix (naturalFiniteModel (d₁ n))
          (naturalFiniteModel (d₁ n)) ℂ) * x n *
        (U₂ n g : Matrix (naturalFiniteModel (d₂ n))
          (naturalFiniteModel (d₂ n)) ℂ)ᴴ) /
      ((d₁ n : ℝ) + d₂ n)) ≤ ε

/-- **Kazhdan transport of asymptotic intertwiners in the exact
manuscript coordinates.**  No root datum is an input: the proof applies
the block reduction and the general transport with the harmless root
`1`. -/
theorem manuscriptIntertwinerTransport :
    ∀ {Γ : Type} {H : Type u} [Group Γ] [Group H]
    (_hT : HasKazhdanPropertyTComplex.{0, uK} Γ)
    (iota : Γ →* H) (s : H)
    (_hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (d₁ d₂ : ℕ → ℕ) (_hd₁ : ∀ n, 0 < d₁ n) (_hd₂ : ∀ n, 0 < d₂ n)
    (U₁ : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d₁ n)) ℂ)
    (U₂ : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d₂ n)) ℂ)
    (_hU₁ : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U₁ n (g * h) : Matrix (naturalFiniteModel (d₁ n))
          (naturalFiniteModel (d₁ n)) ℂ) -
        (U₁ n g : Matrix (naturalFiniteModel (d₁ n))
          (naturalFiniteModel (d₁ n)) ℂ) * U₁ n h‖ ≤ ε)
    (_hU₂ : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U₂ n (g * h) : Matrix (naturalFiniteModel (d₂ n))
          (naturalFiniteModel (d₂ n)) ℂ) -
        (U₂ n g : Matrix (naturalFiniteModel (d₂ n))
          (naturalFiniteModel (d₂ n)) ℂ) * U₂ n h‖ ≤ ε)
    (x : ∀ n, Matrix (naturalFiniteModel (d₁ n))
      (naturalFiniteModel (d₂ n)) ℂ)
    (_hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M)
    (_hx : ∀ γ : Γ, NaturalHSIntertwinerVanishing d₁ d₂ U₁ U₂ x (iota γ)),
    ∀ γ : Γ, NaturalHSIntertwinerVanishing d₁ d₂ U₁ U₂
      (fun n ↦ (U₁ n s : Matrix (naturalFiniteModel (d₁ n))
          (naturalFiniteModel (d₁ n)) ℂ) * x n *
        (U₂ n s : Matrix (naturalFiniteModel (d₂ n))
          (naturalFiniteModel (d₂ n)) ℂ)ᴴ) (iota γ) := by
  intro Γ H _ _ hT iota s hs d₁ d₂ hd₁ hd₂ U₁ U₂ hU₁ hU₂ x hbound hx
  let B₁ : OpAlmostRepresentation H := {
    model := fun n ↦ naturalFiniteModel (d₁ n)
    modelNonempty := fun n ↦ by simpa using hd₁ n
    map := U₁
    asymptoticallyMultiplicative := hU₁ }
  let B₂ : OpAlmostRepresentation H := {
    model := fun n ↦ naturalFiniteModel (d₂ n)
    modelNonempty := fun n ↦ by simpa using hd₂ n
    map := U₂
    asymptoticallyMultiplicative := hU₂ }
  let C : KazhdanCompressionCore Γ H := {
    iota := iota
    t := s
    c := 1
    kazhdan := hasKazhdanPropertyT_iff_textbook.mpr hT
    compresses := hs
    comm_c := fun γ ↦ Commute.one_left (iota γ) }
  have hcard : ∀ n : ℕ,
      ((Fintype.card (naturalFiniteModel (d₁ n)) : ℝ) +
        Fintype.card (naturalFiniteModel (d₂ n))) =
        (d₁ n : ℝ) + d₂ n := by
    intro n
    simp
  have hpos : ∀ n : ℕ, (0 : ℝ) < (d₁ n : ℝ) + d₂ n := by
    intro n
    have h : 0 < d₁ n + d₂ n := Nat.add_pos_left (hd₁ n) _
    exact_mod_cast h
  have hxI : IsAsymptoticIntertwiner B₁ B₂ C x := by
    intro γ ε hε
    obtain ⟨N, hN⟩ := hx γ (Real.sqrt ε) (Real.sqrt_pos.2 hε)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hsq := hN n hn
    have hmass : 0 ≤ rectMass (x n -
        (U₁ n (iota γ) : Matrix (naturalFiniteModel (d₁ n))
          (naturalFiniteModel (d₁ n)) ℂ) * x n *
        (U₂ n (iota γ) : Matrix (naturalFiniteModel (d₂ n))
          (naturalFiniteModel (d₂ n)) ℂ)ᴴ) := rectMass_nonneg _
    have hdiv : rectMass (x n -
        (U₁ n (iota γ) : Matrix (naturalFiniteModel (d₁ n))
          (naturalFiniteModel (d₁ n)) ℂ) * x n *
        (U₂ n (iota γ) : Matrix (naturalFiniteModel (d₂ n))
          (naturalFiniteModel (d₂ n)) ℂ)ᴴ) / ((d₁ n : ℝ) + d₂ n) ≤ ε := by
      calc
        rectMass (x n -
            (U₁ n (iota γ) : Matrix (naturalFiniteModel (d₁ n))
              (naturalFiniteModel (d₁ n)) ℂ) * x n *
            (U₂ n (iota γ) : Matrix (naturalFiniteModel (d₂ n))
              (naturalFiniteModel (d₂ n)) ℂ)ᴴ) / ((d₁ n : ℝ) + d₂ n) =
            (Real.sqrt (rectMass (x n -
              (U₁ n (iota γ) : Matrix (naturalFiniteModel (d₁ n))
                (naturalFiniteModel (d₁ n)) ℂ) * x n *
              (U₂ n (iota γ) : Matrix (naturalFiniteModel (d₂ n))
                (naturalFiniteModel (d₂ n)) ℂ)ᴴ) /
              ((d₁ n : ℝ) + d₂ n))) ^ 2 :=
          (Real.sq_sqrt (div_nonneg hmass (hpos n).le)).symm
        _ ≤ (Real.sqrt ε) ^ 2 :=
          (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).2 hsq
        _ = ε := Real.sq_sqrt hε.le
    have hgoal := (div_le_iff₀ (hpos n)).mp hdiv
    rw [← hcard n] at hgoal
    exact hgoal
  have hxB : IsUniformlyBoundedRect B₁ B₂ x := hbound
  have htrans := intertwiner_transport B₁ B₂ C x hxI hxB
  intro γ ε hε
  obtain ⟨N, hN⟩ := htrans γ (ε ^ 2) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hval := hN n hn
  rw [hcard n] at hval
  have hdiv : rectMass ((fun n ↦
      (U₁ n s : Matrix (naturalFiniteModel (d₁ n))
        (naturalFiniteModel (d₁ n)) ℂ) * x n *
      (U₂ n s : Matrix (naturalFiniteModel (d₂ n))
        (naturalFiniteModel (d₂ n)) ℂ)ᴴ) n -
      (U₁ n (iota γ) : Matrix (naturalFiniteModel (d₁ n))
        (naturalFiniteModel (d₁ n)) ℂ) *
        ((fun n ↦ (U₁ n s : Matrix (naturalFiniteModel (d₁ n))
          (naturalFiniteModel (d₁ n)) ℂ) * x n *
          (U₂ n s : Matrix (naturalFiniteModel (d₂ n))
            (naturalFiniteModel (d₂ n)) ℂ)ᴴ) n) *
        (U₂ n (iota γ) : Matrix (naturalFiniteModel (d₂ n))
          (naturalFiniteModel (d₂ n)) ℂ)ᴴ) /
      ((d₁ n : ℝ) + d₂ n) ≤ ε ^ 2 :=
    (div_le_iff₀ (hpos n)).mpr hval
  have hsqrt := Real.sqrt_le_sqrt hdiv
  rw [Real.sqrt_sq hε.le] at hsqrt
  exact hsqrt

end IntertwinerKazhdanTransport
end GroupApproximation
