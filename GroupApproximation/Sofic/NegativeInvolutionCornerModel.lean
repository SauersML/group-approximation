import GroupApproximation.Sofic.KazhdanCornerDiagonal

/-!
# Polar-corrected negative involution corners

This file isolates the diagonal-extraction step needed after cutting an
operator-norm almost representation by the negative spectral sector of a
rounded central involution.  The spectral construction supplies a family of
nonzero finite corners and uncorrected compressions.  The present file turns
any such family into a genuine `OpAlmostRepresentation` by polar correction,
while retaining the assertion that the marked involution converges to `-1`.

The input structure is intentionally narrow.  Its fields are exactly the
four estimates furnished by diagonalizing the rounded involution and using
the two off-diagonal leakage bounds.  In particular, it contains no
separation assumption.
-/

namespace GroupApproximation
namespace NegativeInvolutionCornerModel

open Matrix
open scoped Matrix.Norms.L2Operator

variable {G : Type*} [Group G]

/-- Uncorrected nonzero finite corners obtained from a rounded negative
spectral sector.  `compression` is contractive, asymptotically unitary and
asymptotically multiplicative.  The distinguished involution `marked`
converges to `-1` on these renormalized corners. -/
structure PolarCornerSetup (G : Type*) [Group G] where
  model : ℕ → FiniteModel
  modelNonempty : ∀ n, 0 < Fintype.card (model n)
  compression : ∀ n, G → Matrix (model n) (model n) ℂ
  compression_norm_le_one : ∀ n g, ‖compression n g‖ ≤ 1
  gram_eventually_small : ∀ (g : G) (η : ℝ), 0 < η → ∃ N, ∀ n ≥ N,
    ‖KazhdanCornerMatrices.cornerGram (compression n g) - 1‖ ≤ η
  multiplicative_eventually : ∀ (g h : G) (η : ℝ), 0 < η → ∃ N, ∀ n ≥ N,
    ‖compression n (g * h) - compression n g * compression n h‖ ≤ η
  marked : G
  marked_eventually_negative : ∀ η : ℝ, 0 < η → ∃ N, ∀ n ≥ N,
    ‖compression n marked + 1‖ ≤ η

/-! ## Construction from reducing eigenvector coordinates -/

/-- Coordinate data produced by diagonalizing the rounded involution.  The
Boolean predicate selects its negative eigencoordinates.  Approximate
centrality supplies the two off-diagonal leakage estimates. -/
structure ReducingCoordinateData (G : Type*) [Group G] where
  approximation : OpAlmostRepresentation G
  keep : ∀ n, approximation.model n → Bool
  keptNonempty : ∀ n, 0 < Fintype.card {i : approximation.model n // keep n i = true}
  basis : ∀ n, Matrix.unitaryGroup (approximation.model n) ℂ
  lowerLeakage : ∀ (g : G) (η : ℝ), 0 < η → ∃ N, ∀ n ≥ N,
    ‖KazhdanCornerMatrices.coordinateBlock
      (fun i ↦ keep n i ≠ true) (fun i ↦ keep n i = true)
      ((basis n : Matrix (approximation.model n) (approximation.model n) ℂ)ᴴ *
        approximation.map n g * basis n)‖ ≤ η
  upperLeakage : ∀ (g : G) (η : ℝ), 0 < η → ∃ N, ∀ n ≥ N,
    ‖KazhdanCornerMatrices.coordinateBlock
      (fun i ↦ keep n i = true) (fun i ↦ keep n i ≠ true)
      ((basis n : Matrix (approximation.model n) (approximation.model n) ℂ)ᴴ *
        approximation.map n g * basis n)‖ ≤ η
  marked : G
  markedNegative : ∀ η : ℝ, 0 < η → ∃ N, ∀ n ≥ N,
    ‖KazhdanCornerMatrices.principalBlock (fun i ↦ keep n i = true)
        ((basis n : Matrix (approximation.model n) (approximation.model n) ℂ)ᴴ *
          approximation.map n marked * basis n) + 1‖ ≤ η

/-- The ambient almost representation in the chosen diagonalizing basis. -/
noncomputable def ReducingCoordinateData.basisMap
    (D : ReducingCoordinateData G) (n : ℕ) (g : G) :
    Matrix (D.approximation.model n) (D.approximation.model n) ℂ :=
  (D.basis n : Matrix (D.approximation.model n) (D.approximation.model n) ℂ)ᴴ *
    D.approximation.map n g * D.basis n

/-- Raw principal compression to the selected negative eigencoordinates. -/
noncomputable def ReducingCoordinateData.compression
    (D : ReducingCoordinateData G) (n : ℕ) (g : G) :
    Matrix {i : D.approximation.model n // D.keep n i = true}
      {i : D.approximation.model n // D.keep n i = true} ℂ :=
  KazhdanCornerMatrices.principalBlock (fun i ↦ D.keep n i = true)
    (D.basisMap n g)

theorem ReducingCoordinateData.basisMap_mem_unitaryGroup
    (D : ReducingCoordinateData G) (n : ℕ) (g : G) :
    D.basisMap n g ∈ Matrix.unitaryGroup (D.approximation.model n) ℂ := by
  have hBstar :
      (D.basis n : Matrix (D.approximation.model n)
        (D.approximation.model n) ℂ)ᴴ ∈
        Matrix.unitaryGroup (D.approximation.model n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem (D.basis n).2
  exact mul_mem (mul_mem hBstar (D.approximation.map n g).2) (D.basis n).2

theorem ReducingCoordinateData.basisMap_star_mul_self
    (D : ReducingCoordinateData G) (n : ℕ) (g : G) :
    (D.basisMap n g)ᴴ * D.basisMap n g = 1 := by
  have h := D.basisMap_mem_unitaryGroup n g
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
  exact h

theorem ReducingCoordinateData.norm_basisMap_mul_defect_eq
    (D : ReducingCoordinateData G) (n : ℕ) (g h : G) :
    ‖D.basisMap n (g * h) - D.basisMap n g * D.basisMap n h‖ =
      ‖(D.approximation.map n (g * h) :
          Matrix (D.approximation.model n) (D.approximation.model n) ℂ) -
        D.approximation.map n g * D.approximation.map n h‖ := by
  have hBstar :
      (D.basis n : Matrix (D.approximation.model n)
        (D.approximation.model n) ℂ)ᴴ ∈
        Matrix.unitaryGroup (D.approximation.model n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem (D.basis n).2
  have hBBstar :
      (D.basis n : Matrix (D.approximation.model n)
        (D.approximation.model n) ℂ) * (D.basis n : Matrix _ _ ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem (D.basis n).2
  rw [basisMap, basisMap, basisMap]
  rw [KazhdanCornerMatrices.unitaryConjugation_mul_defect_eq hBBstar]
  simpa only [Matrix.conjTranspose_conjTranspose] using
    KazhdanCornerMatrices.norm_unitary_conjugate hBstar
      (D := (D.approximation.map n (g * h) : Matrix _ _ ℂ) -
        D.approximation.map n g * D.approximation.map n h)

/-- Principal compression to the negative coordinates is contractive. -/
theorem ReducingCoordinateData.norm_compression_le_one
    (D : ReducingCoordinateData G) (n : ℕ) (g : G) :
    ‖D.compression n g‖ ≤ 1 := by
  exact (KazhdanCornerMatrices.norm_principalBlock_le
    (fun i ↦ D.keep n i = true) (D.basisMap n g)).trans_eq
      (CStarRing.norm_of_mem_unitary (D.basisMap_mem_unitaryGroup n g))

/-- The lower leakage estimate makes every fixed compressed Gram defect
vanish. -/
theorem ReducingCoordinateData.gram_eventually_small
    (D : ReducingCoordinateData G) (g : G) (η : ℝ) (hη : 0 < η) :
    ∃ N, ∀ n ≥ N,
      ‖KazhdanCornerMatrices.cornerGram (D.compression n g) - 1‖ ≤ η := by
  obtain ⟨N, hN⟩ := D.lowerLeakage g (Real.sqrt η) (Real.sqrt_pos.2 hη)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hbase := KazhdanCornerMatrices.norm_principalBlock_gram_sub_one_le
    (fun i ↦ D.keep n i = true) (D.basisMap n g)
      (D.basisMap_star_mul_self n g)
  calc
    ‖KazhdanCornerMatrices.cornerGram (D.compression n g) - 1‖ ≤
        ‖KazhdanCornerMatrices.coordinateBlock
          (fun i ↦ D.keep n i ≠ true) (fun i ↦ D.keep n i = true)
          (D.basisMap n g)‖ ^ 2 := hbase
    _ ≤ (Real.sqrt η) ^ 2 := by
      nlinarith [norm_nonneg (KazhdanCornerMatrices.coordinateBlock
        (fun i ↦ D.keep n i ≠ true) (fun i ↦ D.keep n i = true)
        (D.basisMap n g)), hN n hn]
    _ = η := Real.sq_sqrt hη.le

/-- Ambient multiplicativity and one off-diagonal leakage estimate imply
multiplicativity of every fixed pair of raw compressions. -/
theorem ReducingCoordinateData.multiplicative_eventually
    (D : ReducingCoordinateData G) (g h : G) (η : ℝ) (hη : 0 < η) :
    ∃ N, ∀ n ≥ N,
      ‖D.compression n (g * h) - D.compression n g * D.compression n h‖ ≤ η := by
  obtain ⟨Nmul, hmul⟩ :=
    D.approximation.asymptoticallyMultiplicative g h (η / 2) (by linarith)
  obtain ⟨Nleak, hleak⟩ := D.upperLeakage g (η / 2) (by linarith)
  refine ⟨max Nmul Nleak, fun n hn ↦ ?_⟩
  have hambient :
      ‖D.basisMap n (g * h) - D.basisMap n g * D.basisMap n h‖ ≤ η / 2 := by
    rw [D.norm_basisMap_mul_defect_eq n g h]
    exact hmul n ((le_max_left _ _).trans hn)
  have hupper :
      ‖KazhdanCornerMatrices.coordinateBlock
        (fun i ↦ D.keep n i = true) (fun i ↦ D.keep n i ≠ true)
        (D.basisMap n g)‖ ≤ η / 2 :=
    hleak n ((le_max_right _ _).trans hn)
  have hlower :
      ‖KazhdanCornerMatrices.coordinateBlock
        (fun i ↦ D.keep n i ≠ true) (fun i ↦ D.keep n i = true)
        (D.basisMap n h)‖ ≤ 1 :=
    (KazhdanCornerMatrices.norm_coordinateBlock_le _ _ _).trans_eq
      (CStarRing.norm_of_mem_unitary (D.basisMap_mem_unitaryGroup n h))
  have hbase := KazhdanCornerMatrices.norm_principalBlock_mul_defect_le
    (fun i ↦ D.keep n i = true) (D.basisMap n (g * h))
      (D.basisMap n g) (D.basisMap n h)
  calc
    ‖D.compression n (g * h) - D.compression n g * D.compression n h‖ ≤
        ‖D.basisMap n (g * h) - D.basisMap n g * D.basisMap n h‖ +
          ‖KazhdanCornerMatrices.coordinateBlock
            (fun i ↦ D.keep n i = true) (fun i ↦ D.keep n i ≠ true)
            (D.basisMap n g)‖ *
          ‖KazhdanCornerMatrices.coordinateBlock
            (fun i ↦ D.keep n i ≠ true) (fun i ↦ D.keep n i = true)
            (D.basisMap n h)‖ := hbase
    _ ≤ η / 2 + (η / 2) * 1 :=
      add_le_add hambient (mul_le_mul hupper hlower (norm_nonneg _) (by linarith))
    _ = η := by ring

/-- Reducing eigenvector coordinates furnish precisely the raw input needed
by the diagonal polar-correction constructor. -/
noncomputable def ReducingCoordinateData.toPolarCornerSetup
    (D : ReducingCoordinateData G) : PolarCornerSetup G where
  model n := ⟨{i : D.approximation.model n // D.keep n i = true},
    inferInstance, inferInstance⟩
  modelNonempty := D.keptNonempty
  compression := D.compression
  compression_norm_le_one := D.norm_compression_le_one
  gram_eventually_small := D.gram_eventually_small
  multiplicative_eventually := D.multiplicative_eventually
  marked := D.marked
  marked_eventually_negative := D.markedNegative

/-- A cofinal diagonal schedule making the first `n + 1` enumerated
compressions uniformly polar-correctable. -/
structure PolarCornerSchedule [Countable G] (D : PolarCornerSetup G) where
  enumerate : ℕ → G
  enumerate_surjective : Function.Surjective enumerate
  stage : ℕ → ℕ
  stage_ge : ∀ n, n ≤ stage n
  gram_close : ∀ n k, k ≤ n →
    ‖KazhdanCornerMatrices.cornerGram
        (D.compression (stage n) (enumerate k)) - 1‖ ≤
      KazhdanCornerMatrices.diagonalTolerance n

/-- Countability gives a schedule on which every fixed compression is
eventually within the standard diagonal tolerance of a unitary. -/
theorem exists_polarCornerSchedule [Countable G] (D : PolarCornerSetup G) :
    Nonempty (PolarCornerSchedule D) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat G
  let F : ℕ → Finset G := fun n ↦ (Finset.range (n + 1)).image e
  have hsimultaneous (n : ℕ) : ∃ N, ∀ m ≥ N, ∀ g ∈ F n,
      ‖KazhdanCornerMatrices.cornerGram (D.compression m g) - 1‖ ≤
        KazhdanCornerMatrices.diagonalTolerance n := by
    apply eventually_finset (F n)
    intro g _
    exact D.gram_eventually_small g
      (KazhdanCornerMatrices.diagonalTolerance n)
      (KazhdanCornerMatrices.diagonalTolerance_pos n)
  let threshold : ℕ → ℕ := fun n ↦ Classical.choose (hsimultaneous n)
  have hthreshold (n : ℕ) : ∀ m ≥ threshold n, ∀ g ∈ F n,
      ‖KazhdanCornerMatrices.cornerGram (D.compression m g) - 1‖ ≤
        KazhdanCornerMatrices.diagonalTolerance n :=
    Classical.choose_spec (hsimultaneous n)
  let stage : ℕ → ℕ := fun n ↦ max n (threshold n)
  refine ⟨{
    enumerate := e
    enumerate_surjective := he
    stage := stage
    stage_ge := fun n ↦ le_max_left _ _
    gram_close := ?_ }⟩
  intro n k hk
  exact hthreshold n (stage n) (le_max_right _ _) (e k)
    (Finset.mem_image.mpr ⟨k, by simp only [Finset.mem_range]; omega, rfl⟩)

/-- A chosen enumeration index for a fixed group element. -/
noncomputable def PolarCornerSchedule.code [Countable G]
    {D : PolarCornerSetup G} (R : PolarCornerSchedule D) (g : G) : ℕ :=
  Classical.choose (R.enumerate_surjective g)

@[simp] theorem PolarCornerSchedule.enumerate_code [Countable G]
    {D : PolarCornerSetup G} (R : PolarCornerSchedule D) (g : G) :
    R.enumerate (R.code g) = g :=
  Classical.choose_spec (R.enumerate_surjective g)

/-- The selected negative corner at diagonal stage `n`. -/
noncomputable abbrev PolarCornerSchedule.model [Countable G]
    {D : PolarCornerSetup G} (R : PolarCornerSchedule D) (n : ℕ) :
    FiniteModel :=
  D.model (R.stage n)

theorem PolarCornerSchedule.model_nonempty [Countable G]
    {D : PolarCornerSetup G} (R : PolarCornerSchedule D) (n : ℕ) :
    0 < Fintype.card (R.model n) :=
  D.modelNonempty (R.stage n)

/-- Polar-correct the active compression.  Before an element enters the
finite exhaustion, initialize it to the identity. -/
noncomputable def PolarCornerSchedule.map [Countable G]
    {D : PolarCornerSetup G} (R : PolarCornerSchedule D)
    (n : ℕ) (g : G) :
    Matrix.unitaryGroup (R.model n) ℂ := by
  by_cases hg : R.code g ≤ n
  · have hclose := R.gram_close n (R.code g) hg
    rw [R.enumerate_code g] at hclose
    exact KazhdanCornerMatrices.polarCorrectUnitary
      (D.compression (R.stage n) g)
      (KazhdanCornerMatrices.cornerGram_isHermitian _)
      (KazhdanCornerMatrices.diagonalTolerance_le_half n) hclose
  · exact 1

/-- Active polar correction differs from the raw compression by at most
twice the diagonal tolerance. -/
theorem PolarCornerSchedule.map_close_of_code_le [Countable G]
    {D : PolarCornerSetup G} (R : PolarCornerSchedule D)
    (n : ℕ) (g : G) (hg : R.code g ≤ n) :
    ‖(R.map n g : Matrix (R.model n) (R.model n) ℂ) -
        D.compression (R.stage n) g‖ ≤
      2 * KazhdanCornerMatrices.diagonalTolerance n := by
  rw [PolarCornerSchedule.map, dif_pos hg]
  exact KazhdanCornerMatrices.norm_polarCorrect_sub_le
    (D.compression (R.stage n) g)
    (KazhdanCornerMatrices.cornerGram_isHermitian _)
    (D.compression_norm_le_one (R.stage n) g)
    (KazhdanCornerMatrices.diagonalTolerance_pos n).le
    (KazhdanCornerMatrices.diagonalTolerance_le_half n) (by
      simpa only [R.enumerate_code g] using
        R.gram_close n (R.code g) hg)

/-- Every fixed corrected map is eventually close to its raw corner
compression. -/
theorem PolarCornerSchedule.map_eventually_close [Countable G]
    {D : PolarCornerSetup G} (R : PolarCornerSchedule D) (g : G) :
    ∃ N, ∀ n ≥ N,
      ‖(R.map n g : Matrix (R.model n) (R.model n) ℂ) -
          D.compression (R.stage n) g‖ ≤
        2 * KazhdanCornerMatrices.diagonalTolerance n :=
  ⟨R.code g, fun n hn ↦ R.map_close_of_code_le n g hn⟩

/-- Scheduled polar corrections remain asymptotically multiplicative in
operator norm. -/
theorem PolarCornerSchedule.map_multiplicative_eventually [Countable G]
    {D : PolarCornerSetup G} (R : PolarCornerSchedule D)
    (g h : G) : ∀ η : ℝ, 0 < η → ∃ N, ∀ n ≥ N,
    ‖(R.map n (g * h) : Matrix (R.model n) (R.model n) ℂ) -
      (R.map n g : Matrix (R.model n) (R.model n) ℂ) * R.map n h‖ ≤ η := by
  intro η hη
  obtain ⟨Nmul, hmul⟩ := D.multiplicative_eventually g h (η / 2) (by linarith)
  obtain ⟨Ntol, htol⟩ :=
    KazhdanCornerMatrices.diagonalTolerance_eventually_le
      (show 0 < η / 12 by linarith)
  let Ncode := max (R.code (g * h)) (max (R.code g) (R.code h))
  refine ⟨max Nmul (max Ntol Ncode), fun n hn ↦ ?_⟩
  have hnMul : Nmul ≤ n := by omega
  have hnTol : Ntol ≤ n := by omega
  have hnCode : Ncode ≤ n := by omega
  have hghActive : R.code (g * h) ≤ n := by dsimp [Ncode] at hnCode; omega
  have hgActive : R.code g ≤ n := by dsimp [Ncode] at hnCode; omega
  have hhActive : R.code h ≤ n := by dsimp [Ncode] at hnCode; omega
  let Wgh : Matrix (R.model n) (R.model n) ℂ := R.map n (g * h)
  let Wg : Matrix (R.model n) (R.model n) ℂ := R.map n g
  let Wh : Matrix (R.model n) (R.model n) ℂ := R.map n h
  let Cgh : Matrix (R.model n) (R.model n) ℂ :=
    D.compression (R.stage n) (g * h)
  let Cg : Matrix (R.model n) (R.model n) ℂ :=
    D.compression (R.stage n) g
  let Ch : Matrix (R.model n) (R.model n) ℂ :=
    D.compression (R.stage n) h
  have hclosegh : ‖Wgh - Cgh‖ ≤
      2 * KazhdanCornerMatrices.diagonalTolerance n :=
    R.map_close_of_code_le n (g * h) hghActive
  have hcloseg : ‖Wg - Cg‖ ≤
      2 * KazhdanCornerMatrices.diagonalTolerance n :=
    R.map_close_of_code_le n g hgActive
  have hcloseh : ‖Wh - Ch‖ ≤
      2 * KazhdanCornerMatrices.diagonalTolerance n :=
    R.map_close_of_code_le n h hhActive
  have hcloseg' : ‖Cg - Wg‖ ≤
      2 * KazhdanCornerMatrices.diagonalTolerance n := by
    rw [show Cg - Wg = -(Wg - Cg) by abel, norm_neg]
    exact hcloseg
  have hcloseh' : ‖Ch - Wh‖ ≤
      2 * KazhdanCornerMatrices.diagonalTolerance n := by
    rw [show Ch - Wh = -(Wh - Ch) by abel, norm_neg]
    exact hcloseh
  have hdefect : ‖Cgh - Cg * Ch‖ ≤ η / 2 :=
    hmul (R.stage n) (hnMul.trans (R.stage_ge n))
  letI : Nonempty (R.model n) :=
    Fintype.card_pos_iff.mp (R.model_nonempty n)
  have hWh : ‖Wh‖ = 1 :=
    CStarRing.norm_of_mem_unitary (R.map n h).2
  have hCg : ‖Cg‖ ≤ 1 := D.compression_norm_le_one (R.stage n) g
  have htermg : ‖Cg - Wg‖ * ‖Wh‖ ≤
      (2 * KazhdanCornerMatrices.diagonalTolerance n) * 1 :=
    mul_le_mul hcloseg' hWh.le (norm_nonneg _)
      (mul_nonneg (by norm_num)
        (KazhdanCornerMatrices.diagonalTolerance_pos n).le)
  have htermh : ‖Cg‖ * ‖Ch - Wh‖ ≤
      1 * (2 * KazhdanCornerMatrices.diagonalTolerance n) :=
    mul_le_mul hCg hcloseh' (norm_nonneg _) (by norm_num)
  have hbase := KazhdanCornerMatrices.norm_mul_defect_of_perturbations
    Wgh Wg Wh Cgh Cg Ch
  have htolerance := htol n hnTol
  dsimp only [Wgh, Wg, Wh] at hbase ⊢
  nlinarith

/-- The polar-corrected negative corners form an operator-norm almost
representation. -/
noncomputable def PolarCornerSchedule.toOpAlmostRepresentation [Countable G]
    {D : PolarCornerSetup G} (R : PolarCornerSchedule D) :
    OpAlmostRepresentation G where
  model := R.model
  modelNonempty := R.model_nonempty
  map := R.map
  asymptoticallyMultiplicative := R.map_multiplicative_eventually

/-- The marked involution still converges to `-1` after diagonal extraction
and polar correction. -/
theorem PolarCornerSchedule.marked_eventually_negative [Countable G]
    {D : PolarCornerSetup G} (R : PolarCornerSchedule D) :
    ∀ η : ℝ, 0 < η → ∃ N, ∀ n ≥ N,
      ‖(R.map n D.marked : Matrix (R.model n) (R.model n) ℂ) + 1‖ ≤ η := by
  intro η hη
  obtain ⟨Nmark, hmark⟩ := D.marked_eventually_negative (η / 2) (by linarith)
  obtain ⟨Ntol, htol⟩ :=
    KazhdanCornerMatrices.diagonalTolerance_eventually_le
      (show 0 < η / 4 by linarith)
  refine ⟨max (R.code D.marked) (max Nmark Ntol), fun n hn ↦ ?_⟩
  have hactive : R.code D.marked ≤ n := by omega
  have hnmark : Nmark ≤ R.stage n := by
    exact (show Nmark ≤ n by omega).trans (R.stage_ge n)
  have hntol : Ntol ≤ n := by omega
  have hclose := R.map_close_of_code_le n D.marked hactive
  have hraw := hmark (R.stage n) hnmark
  calc
    ‖(R.map n D.marked : Matrix (R.model n) (R.model n) ℂ) + 1‖ =
        ‖((R.map n D.marked : Matrix (R.model n) (R.model n) ℂ) -
          D.compression (R.stage n) D.marked) +
          (D.compression (R.stage n) D.marked + 1)‖ := by
            congr 1
            abel
    _ ≤ ‖(R.map n D.marked : Matrix (R.model n) (R.model n) ℂ) -
          D.compression (R.stage n) D.marked‖ +
        ‖D.compression (R.stage n) D.marked + 1‖ := norm_add_le _ _
    _ ≤ 2 * KazhdanCornerMatrices.diagonalTolerance n + η / 2 :=
      add_le_add hclose hraw
    _ ≤ η := by
      have := htol n hntol
      linarith

/-- Final packaged output of the negative-corner construction. -/
structure NegativeCornerRepresentation (G : Type*) [Group G] where
  approximation : OpAlmostRepresentation G
  marked : G
  marked_eventually_negative : ∀ η : ℝ, 0 < η → ∃ N, ∀ n ≥ N,
    ‖(approximation.map n marked :
        Matrix (approximation.model n) (approximation.model n) ℂ) + 1‖ ≤ η

/-- Diagonal extraction and polar correction turn any raw negative-corner
setup into an operator-norm almost representation whose marked involution is
uniformly the negative scalar asymptotically. -/
theorem PolarCornerSetup.exists_negativeCornerRepresentation [Countable G]
    (D : PolarCornerSetup G) :
    Nonempty (NegativeCornerRepresentation G) := by
  let R : PolarCornerSchedule D := Classical.choice (exists_polarCornerSchedule D)
  exact ⟨{
    approximation := R.toOpAlmostRepresentation
    marked := D.marked
    marked_eventually_negative := R.marked_eventually_negative }⟩


end NegativeInvolutionCornerModel
end GroupApproximation
