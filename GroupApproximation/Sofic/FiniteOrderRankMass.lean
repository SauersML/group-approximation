import GroupApproximation.Sofic.TorsionActiveCore

/-!
# Rank--mass lower bounds for finite-order unitaries

This file supplies the spectral half of active-core reblocking.  Its first
ingredient is a basis-free Frobenius estimate: every idempotent matrix has
Frobenius mass at least its rank, whether or not it is orthogonal.
-/

namespace GroupApproximation
namespace FiniteOrderRankMass

open Matrix InvolutionRankMass RankNormalizedHilbertization
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

omit [DecidableEq Y] in
/-- The real trace of the square of a matrix is bounded by its Frobenius
mass.  Pair the `(i,j)` and `(j,i)` summands and use `2ab ≤ a²+b²`. -/
theorem re_trace_sq_le_matMass (P : Matrix Y Y ℂ) :
    ((P * P).trace).re ≤ ScaledKazhdanTransport.matMass P := by
  rw [Matrix.trace, Complex.re_sum]
  calc
    ∑ i : Y, ((P * P) i i).re =
        ∑ i : Y, ∑ j : Y, (P i j * P j i).re := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.mul_apply, Complex.re_sum]
    _ ≤ ∑ i : Y, ∑ j : Y,
          (Complex.normSq (P i j) + Complex.normSq (P j i)) / 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hre : (P i j * P j i).re ≤ ‖P i j‖ * ‖P j i‖ := by
        calc
          (P i j * P j i).re ≤ ‖P i j * P j i‖ :=
            Complex.re_le_norm _
          _ = ‖P i j‖ * ‖P j i‖ := norm_mul _ _
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      nlinarith [sq_nonneg (‖P i j‖ - ‖P j i‖)]
    _ = ScaledKazhdanTransport.matMass P := by
      unfold ScaledKazhdanTransport.matMass
      have hswap : (∑ i : Y, ∑ j : Y, Complex.normSq (P j i)) =
          ∑ i : Y, ∑ j : Y, Complex.normSq (P i j) := Finset.sum_comm
      calc
        (∑ i : Y, ∑ j : Y,
            (Complex.normSq (P i j) + Complex.normSq (P j i)) / 2) =
            ∑ i : Y, ((∑ j : Y, Complex.normSq (P i j)) +
              (∑ j : Y, Complex.normSq (P j i))) / 2 := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [add_div, Finset.sum_add_distrib, ← Finset.sum_div]
        _ = ((∑ i : Y, ∑ j : Y, Complex.normSq (P i j)) +
              (∑ i : Y, ∑ j : Y, Complex.normSq (P j i))) / 2 := by
          simp only [add_div, Finset.sum_add_distrib, ← Finset.sum_div]
        _ = ∑ i : Y, ∑ j : Y, Complex.normSq (P i j) := by
          rw [hswap]
          ring

/-- Every idempotent has Frobenius mass at least its rank.  Orthogonality is
not required. -/
theorem rank_le_matMass_of_idempotent {P : Matrix Y Y ℂ}
    (hP : P * P = P) :
    (P.rank : ℝ) ≤ ScaledKazhdanTransport.matMass P := by
  have hidem : IsIdempotentElem P.mulVecLin := by
    show P.mulVecLin * P.mulVecLin = P.mulVecLin
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hP]
  have hproj : LinearMap.IsProj (LinearMap.range P.mulVecLin) P.mulVecLin :=
    LinearMap.IsIdempotentElem.isProj_range _ hidem
  have htr : LinearMap.trace ℂ (Y → ℂ) P.mulVecLin = ((P.rank : ℕ) : ℂ) :=
    hproj.trace
  have hmat : LinearMap.trace ℂ (Y → ℂ) P.mulVecLin = P.trace := by
    rw [← Matrix.toLin'_apply']
    exact Matrix.trace_toLin'_eq P
  have htrace : P.trace = ((P.rank : ℕ) : ℂ) := hmat.symm.trans htr
  calc
    (P.rank : ℝ) = ((P * P).trace).re := by rw [hP, htrace]; simp
    _ ≤ ScaledKazhdanTransport.matMass P := re_trace_sq_le_matMass P

/-! ## The finite-order geometric idempotent -/

/-- Normalized geometric average of the first `m` powers. -/
def torsionAverage (R : Matrix Y Y ℂ) (m : ℕ) : Matrix Y Y ℂ :=
  ((m : ℂ)⁻¹) • ∑ k ∈ Finset.range m, R ^ k

/-- A polynomial antiderivative for `torsionAverage R m - 1`. -/
def torsionAntiderivative (R : Matrix Y Y ℂ) (m : ℕ) : Matrix Y Y ℂ :=
  ((m : ℂ)⁻¹) •
    ∑ k ∈ Finset.range m, ∑ j ∈ Finset.range k, R ^ j

/-- The explicit polynomial antiderivative identity
`(R-1)Q = average(R)-1`. -/
theorem sub_one_mul_torsionAntiderivative
    (R : Matrix Y Y ℂ) (m : ℕ) (hm : 0 < m) :
    (R - 1) * torsionAntiderivative R m = torsionAverage R m - 1 := by
  unfold torsionAntiderivative torsionAverage
  rw [Matrix.mul_smul]
  rw [Finset.mul_sum]
  simp_rw [mul_geom_sum]
  rw [Finset.sum_sub_distrib]
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hconst : (∑ _k ∈ Finset.range m, (1 : Matrix Y Y ℂ)) =
      (m : ℂ) • (1 : Matrix Y Y ℂ) := by
    ext i j
    simp [Matrix.one_apply, smul_eq_mul]
  rw [hconst, smul_sub]
  have hcoef : (m : ℂ)⁻¹ * (m : ℂ) = 1 := inv_mul_cancel₀ hm0
  rw [smul_smul, hcoef, one_smul]

/-- The geometric average is annihilated by `R-1` when `R^m=1`. -/
theorem sub_one_mul_torsionAverage
    (R : Matrix Y Y ℂ) (m : ℕ) (hpow : R ^ m = 1) :
    (R - 1) * torsionAverage R m = 0 := by
  unfold torsionAverage
  rw [Matrix.mul_smul, mul_geom_sum, hpow, sub_self, smul_zero]

/-- The geometric average is also annihilated on the right. -/
theorem torsionAverage_mul_sub_one
    (R : Matrix Y Y ℂ) (m : ℕ) (hpow : R ^ m = 1) :
    torsionAverage R m * (R - 1) = 0 := by
  unfold torsionAverage
  rw [Matrix.smul_mul, geom_sum_mul, hpow, sub_self, smul_zero]

/-- The finite-order geometric average is idempotent. -/
theorem torsionAverage_idempotent
    (R : Matrix Y Y ℂ) (m : ℕ) (hm : 0 < m) (hpow : R ^ m = 1) :
    torsionAverage R m * torsionAverage R m = torsionAverage R m := by
  let A := torsionAverage R m
  let Q := torsionAntiderivative R m
  have hAQ : A - 1 = (R - 1) * Q := by
    exact (sub_one_mul_torsionAntiderivative R m hm).symm
  have hAD : A * (R - 1) = 0 := torsionAverage_mul_sub_one R m hpow
  have hzero : A * (A - 1) = 0 := by
    rw [hAQ, ← Matrix.mul_assoc, hAD, zero_mul]
  apply sub_eq_zero.mp
  calc
    A * A - A = A * (A - 1) := by noncomm_ring
    _ = 0 := hzero

/-- The complement of the finite-order average is an idempotent. -/
theorem one_sub_torsionAverage_idempotent
    (R : Matrix Y Y ℂ) (m : ℕ) (hm : 0 < m) (hpow : R ^ m = 1) :
    (1 - torsionAverage R m) * (1 - torsionAverage R m) =
      1 - torsionAverage R m := by
  have hA := torsionAverage_idempotent R m hm hpow
  calc
    (1 - torsionAverage R m) * (1 - torsionAverage R m) =
        1 - torsionAverage R m - torsionAverage R m +
          torsionAverage R m * torsionAverage R m := by noncomm_ring
    _ = 1 - torsionAverage R m - torsionAverage R m +
          torsionAverage R m := by rw [hA]
    _ = 1 - torsionAverage R m := by abel

/-- The displacement and the complement of the geometric average have the
same rank. -/
theorem rank_sub_one_eq_rank_one_sub_torsionAverage
    (R : Matrix Y Y ℂ) (m : ℕ) (hm : 0 < m) (hpow : R ^ m = 1) :
    (R - 1).rank = (1 - torsionAverage R m).rank := by
  let A := torsionAverage R m
  let Q := torsionAntiderivative R m
  have hDA : (R - 1) * A = 0 := sub_one_mul_torsionAverage R m hpow
  have hDfactor : R - 1 = (R - 1) * (1 - A) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hDA, sub_zero]
  have hQ : (R - 1) * Q = A - 1 :=
    sub_one_mul_torsionAntiderivative R m hm
  have hPfactor : 1 - A = -(R - 1) * Q := by
    rw [Matrix.neg_mul, hQ]
    abel
  apply le_antisymm
  · rw [hDfactor]
    exact Matrix.rank_mul_le_right _ _
  · rw [hPfactor]
    exact (Matrix.rank_mul_le_left _ _).trans_eq
      (InvolutionCollapseMetric.rank_neg (R - 1))

/-- Finite-order displacement mass controls its active rank, with the norm of
the explicit antiderivative as the only constant. -/
theorem rank_le_sq_norm_torsionAntiderivative_mul_matMass
    (R : Matrix Y Y ℂ) (m : ℕ) (hm : 0 < m) (hpow : R ^ m = 1) :
    ((R - 1).rank : ℝ) ≤
      ‖torsionAntiderivative R m‖ ^ 2 * ScaledKazhdanTransport.matMass (R - 1) := by
  let A := torsionAverage R m
  let Q := torsionAntiderivative R m
  have hPidem : (1 - A) * (1 - A) = 1 - A :=
    one_sub_torsionAverage_idempotent R m hm hpow
  have hrank : (R - 1).rank = (1 - A).rank :=
    rank_sub_one_eq_rank_one_sub_torsionAverage R m hm hpow
  have hQ : (R - 1) * Q = A - 1 :=
    sub_one_mul_torsionAntiderivative R m hm
  have hmassEq : ScaledKazhdanTransport.matMass (1 - A) =
      ScaledKazhdanTransport.matMass ((R - 1) * Q) := by
    rw [hQ]
    have hneg : 1 - A = -(A - 1) := by abel
    rw [hneg]
    exact ScaledKazhdanTransport.matMass_neg (A - 1)
  calc
    ((R - 1).rank : ℝ) = ((1 - A).rank : ℝ) := by rw [hrank]
    _ ≤ ScaledKazhdanTransport.matMass (1 - A) :=
      rank_le_matMass_of_idempotent hPidem
    _ = ScaledKazhdanTransport.matMass ((R - 1) * Q) := hmassEq
    _ ≤ ‖Q‖ ^ 2 * ScaledKazhdanTransport.matMass (R - 1) :=
      ScaledKazhdanTransport.matMass_mul_le_right (R - 1) Q

/-- A geometric sum of powers of a unitary has norm at most its length. -/
theorem norm_geom_sum_le [Nonempty Y]
    (R : Matrix.unitaryGroup Y ℂ) (k : ℕ) :
    ‖∑ j ∈ Finset.range k, ((R : Matrix Y Y ℂ) ^ j)‖ ≤ (k : ℝ) := by
  calc
    ‖∑ j ∈ Finset.range k, ((R : Matrix Y Y ℂ) ^ j)‖ ≤
        ∑ j ∈ Finset.range k, ‖((R : Matrix Y Y ℂ) ^ j)‖ :=
      norm_sum_le _ _
    _ = ∑ _j ∈ Finset.range k, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact CStarRing.norm_of_mem_unitary (pow_mem R.prop j)
    _ = (k : ℝ) := by simp

/-- The polynomial antiderivative has the uniform bound `‖Q‖ ≤ m`. -/
theorem norm_torsionAntiderivative_le
    [Nonempty Y] (R : Matrix.unitaryGroup Y ℂ) (m : ℕ) (hm : 0 < m) :
    ‖torsionAntiderivative (R : Matrix Y Y ℂ) m‖ ≤ (m : ℝ) := by
  unfold torsionAntiderivative
  have hsum :
      ‖∑ k ∈ Finset.range m,
          ∑ j ∈ Finset.range k, ((R : Matrix Y Y ℂ) ^ j)‖ ≤
        (m : ℝ) * (m : ℝ) := by
    calc
      ‖∑ k ∈ Finset.range m,
          ∑ j ∈ Finset.range k, ((R : Matrix Y Y ℂ) ^ j)‖ ≤
          ∑ k ∈ Finset.range m,
            ‖∑ j ∈ Finset.range k, ((R : Matrix Y Y ℂ) ^ j)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range m, (m : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact (norm_geom_sum_le R k).trans (by
          exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hk))
      _ = (m : ℝ) * (m : ℝ) := by simp
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hscalar : ‖((m : ℂ)⁻¹)‖ = ((m : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  rw [norm_smul, hscalar]
  calc
    (m : ℝ)⁻¹ *
        ‖∑ k ∈ Finset.range m,
          ∑ j ∈ Finset.range k, ((R : Matrix Y Y ℂ) ^ j)‖ ≤
        (m : ℝ)⁻¹ * ((m : ℝ) * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hmR.le)
    _ = (m : ℝ) := by field_simp

/-- **Finite-order rank--mass gap.**  If a unitary has order dividing the
positive integer `m`, then its displacement has Frobenius mass at least its
active rank divided by `m²`. -/
theorem rank_le_order_sq_mul_matMass
    [Nonempty Y] (R : Matrix.unitaryGroup Y ℂ) (m : ℕ) (hm : 0 < m)
    (hpow : R ^ m = 1) :
    ((((R : Matrix Y Y ℂ) - 1).rank : ℝ)) ≤
      (m : ℝ) ^ 2 *
        ScaledKazhdanTransport.matMass ((R : Matrix Y Y ℂ) - 1) := by
  have hpowM : (R : Matrix Y Y ℂ) ^ m = 1 := by
    change (((R ^ m : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ)) = 1
    rw [hpow]
    rfl
  have hbase := rank_le_sq_norm_torsionAntiderivative_mul_matMass
    (R : Matrix Y Y ℂ) m hm hpowM
  have hnorm := norm_torsionAntiderivative_le R m hm
  have hsq : ‖torsionAntiderivative (R : Matrix Y Y ℂ) m‖ ^ 2 ≤
      (m : ℝ) ^ 2 := by
    nlinarith [norm_nonneg (torsionAntiderivative (R : Matrix Y Y ℂ) m)]
  exact hbase.trans (mul_le_mul_of_nonneg_right hsq
    (ScaledKazhdanTransport.matMass_nonneg _))

/-! ## Finite order survives active-core restriction -/

/-- Restricting and orthonormally coordinatizing a packet unitary preserves
every exact power relation. -/
theorem activeCoreMatrix_pow_eq_one
    {I : Type*} [Fintype I]
    (W : I → Matrix.unitaryGroup Y ℂ) (i : I) (m : ℕ)
    (hpow : (W i) ^ m = 1) :
    (TorsionActiveCore.activeCoreMatrix W i) ^ m = 1 := by
  let K := TorsionActiveCore.activeEuclideanSubspace W
  let b : Module.Basis (Fin (Module.finrank ℂ K)) ℂ K :=
    (stdOrthonormalBasis ℂ K).toBasis
  let e := TorsionActiveCore.activeCoreLinearIsometryEquiv W i
  have hepow_apply : ∀ (k : ℕ) (x : K),
      ((((e.toLinearEquiv.toLinearMap) ^ k) x : K) : EuclideanSpace ℂ Y) =
        Matrix.toEuclideanLin ((((W i) ^ k : Matrix.unitaryGroup Y ℂ) :
          Matrix Y Y ℂ)) (x : EuclideanSpace ℂ Y) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ, Module.End.mul_apply, ih]
        change Matrix.toEuclideanLin ((W i : Matrix Y Y ℂ) ^ k)
            (Matrix.toEuclideanLin (W i : Matrix Y Y ℂ) x) =
          Matrix.toEuclideanLin (((W i : Matrix.unitaryGroup Y ℂ) ^ (k + 1) :
            Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) x
        ext j
        change ((((W i : Matrix Y Y ℂ) ^ k) *ᵥ
          ((W i : Matrix Y Y ℂ) *ᵥ x.1.ofLp)) j) = _
        rw [Matrix.mulVec_mulVec, ← pow_succ]
        rfl
  apply Subtype.ext
  change (LinearMap.toMatrix b b e.toLinearEquiv.toLinearMap) ^ m = 1
  rw [LinearMap.toMatrix_pow]
  rw [← LinearMap.toMatrix_id b]
  apply congrArg (LinearMap.toMatrix b b)
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [hepow_apply]
  rw [hpow]
  ext j
  simp

/-- **Active-rank retention.**  For a positive exact power relation, passing
to the common active core loses none of the distinguished unitary's
displacement rank.  The inverse on the displacement range is supplied by the
finite geometric projector, so no spectral theorem is used. -/
theorem rank_le_activeCoreMatrix_rank
    {I : Type*} [Fintype I]
    (W : I → Matrix.unitaryGroup Y ℂ) (i : I) (m : ℕ) (hm : 0 < m)
    (hpow : (W i) ^ m = 1) :
    (((W i : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) - 1).rank ≤
      (((TorsionActiveCore.activeCoreMatrix W i :
          Matrix.unitaryGroup (TorsionActiveCore.ActiveCoreIndex W) ℂ) :
            Matrix (TorsionActiveCore.ActiveCoreIndex W)
              (TorsionActiveCore.ActiveCoreIndex W) ℂ) - 1).rank := by
  let D : Matrix Y Y ℂ := (W i : Matrix Y Y ℂ) - 1
  let A : Matrix Y Y ℂ := torsionAverage (W i : Matrix Y Y ℂ) m
  let Q : Matrix Y Y ℂ := torsionAntiderivative (W i : Matrix Y Y ℂ) m
  let K := TorsionActiveCore.activeEuclideanSubspace W
  let e := TorsionActiveCore.activeCoreLinearIsometryEquiv W i
  let dK : K →ₗ[ℂ] K := e.toLinearEquiv.toLinearMap - LinearMap.id
  have hpowM : (W i : Matrix Y Y ℂ) ^ m = 1 := by
    change ((((W i) ^ m : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ)) = 1
    rw [hpow]
    rfl
  have hDA : D * A = 0 := by
    exact sub_one_mul_torsionAverage (W i : Matrix Y Y ℂ) m hpowM
  have hDfactor : D * (1 - A) = D := by
    rw [Matrix.mul_sub, Matrix.mul_one, hDA, sub_zero]
  have hQ : D * Q = A - 1 := by
    exact sub_one_mul_torsionAntiderivative (W i : Matrix Y Y ℂ) m hm
  have hPfactor : 1 - A = -D * Q := by
    rw [Matrix.neg_mul, hQ]
    abel
  let toCore : LinearMap.range D.mulVecLin →ₗ[ℂ] K :=
    { toFun := fun z ↦ ⟨(EuclideanSpace.equiv Y ℂ).symm z.1, by
          change (EuclideanSpace.equiv Y ℂ).symm z.1 ∈
            TorsionActiveCore.activeEuclideanSubspace W
          rw [TorsionActiveCore.activeEuclideanSubspace]
          refine ⟨z.1, ?_, rfl⟩
          rcases z.2 with ⟨y, hy⟩
          rw [← hy]
          change (((W i : Matrix Y Y ℂ) - 1) *ᵥ y) ∈
            TorsionActiveCore.activeSubspace W
          exact TorsionActiveCore.displacement_mem_activeSubspace W i y⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact (EuclideanSpace.equiv Y ℂ).symm.map_add x.1 y.1
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact (EuclideanSpace.equiv Y ℂ).symm.map_smul c x.1 }
  have htoCore_range (z : LinearMap.range D.mulVecLin) :
      toCore z ∈ LinearMap.range dK := by
    rcases z.2 with ⟨y, hy⟩
    let xAlg : Y → ℂ := (1 - A) *ᵥ y
    have hxAlg : xAlg ∈ TorsionActiveCore.activeSubspace W := by
      have hx : xAlg = -(D *ᵥ (Q *ᵥ y)) := by
        dsimp [xAlg]
        rw [hPfactor, Matrix.neg_mul, Matrix.mulVec_mulVec,
          Matrix.neg_mulVec]
      rw [hx]
      exact (TorsionActiveCore.activeSubspace W).neg_mem
        (TorsionActiveCore.displacement_mem_activeSubspace W i (Q *ᵥ y))
    let xCore : K := ⟨(EuclideanSpace.equiv Y ℂ).symm xAlg, by
      change (EuclideanSpace.equiv Y ℂ).symm xAlg ∈
        TorsionActiveCore.activeEuclideanSubspace W
      rw [TorsionActiveCore.activeEuclideanSubspace]
      exact ⟨xAlg, hxAlg, rfl⟩⟩
    refine ⟨xCore, ?_⟩
    apply Subtype.ext
    rw [TorsionActiveCore.activeCoreLinearIsometryEquiv_sub_one_coe]
    apply (EuclideanSpace.equiv Y ℂ).injective
    change D *ᵥ xAlg = z.1
    dsimp [xAlg]
    rw [Matrix.mulVec_mulVec, hDfactor]
    exact hy
  let f : LinearMap.range D.mulVecLin →ₗ[ℂ] LinearMap.range dK :=
    { toFun := fun z ↦ ⟨toCore z, htoCore_range z⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact toCore.map_add x y
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact toCore.map_smul c x }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply (EuclideanSpace.equiv Y ℂ).symm.injective
    have hcore : toCore x = toCore y := congrArg Subtype.val hxy
    exact congrArg Subtype.val hcore
  have hfinrank := LinearMap.finrank_le_finrank_of_injective hf
  unfold TorsionActiveCore.activeCoreMatrix
  rw [TorsionActiveCore.rank_orthonormalMatrix_sub_one]
  change Module.finrank ℂ (LinearMap.range D.mulVecLin) ≤
    Module.finrank ℂ (LinearMap.range dK)
  exact hfinrank

/-- **Quantitative active-core reblocking.**  A finite conjugate-word packet
containing a nontrivial finite-order unitary compresses to a common invariant
block whose dimension is at most `totalWordLength` times the original active
rank.  On that block the distinguished unitary has a normalized squared
Hilbert--Schmidt gap bounded uniformly away from zero, in the denominator-free
form `1 ≤ m² L ‖R|K - 1‖₂²`. -/
theorem activeCore_reblocking_dimension_and_hsGap
    {I : Type*} [Fintype I]
    (R : Matrix.unitaryGroup Y ℂ)
    (words : I → List (Matrix.unitaryGroup Y ℂ × Bool))
    (i₀ : I) (hi₀ : TorsionActiveCore.conjugateWord R (words i₀) = R)
    (m : ℕ) (hm : 0 < m) (hpow : R ^ m = 1)
    (hrank : 0 < (((R : Matrix Y Y ℂ) - 1).rank)) :
    let W := TorsionActiveCore.conjugateWordPacket R words
    Fintype.card (TorsionActiveCore.activeCoreModel W) ≤
        TorsionActiveCore.totalWordLength words *
          ((R : Matrix Y Y ℂ) - 1).rank ∧
      1 ≤ (m : ℝ) ^ 2 * (TorsionActiveCore.totalWordLength words : ℝ) *
        hsNormSq (TorsionActiveCore.activeCoreModel W)
          (((TorsionActiveCore.activeCoreModelMatrix W i₀ :
              Matrix.unitaryGroup (TorsionActiveCore.activeCoreModel W) ℂ) :
                Matrix (TorsionActiveCore.activeCoreModel W)
                  (TorsionActiveCore.activeCoreModel W) ℂ) - 1) := by
  let W := TorsionActiveCore.conjugateWordPacket R words
  let S := TorsionActiveCore.activeCoreModel W
  let U := TorsionActiveCore.activeCoreMatrix W i₀
  let E : Matrix (TorsionActiveCore.ActiveCoreIndex W)
      (TorsionActiveCore.ActiveCoreIndex W) ℂ :=
    (U : Matrix (TorsionActiveCore.ActiveCoreIndex W)
      (TorsionActiveCore.ActiveCoreIndex W) ℂ) - 1
  have hWi : W i₀ = R := hi₀
  have hdim : Fintype.card S ≤
      TorsionActiveCore.totalWordLength words *
        ((R : Matrix Y Y ℂ) - 1).rank := by
    exact TorsionActiveCore.card_activeCoreModel_conjugateWordPacket_le R words
  have hpowW : (W i₀) ^ m = 1 := by rw [hWi, hpow]
  have hretain : ((R : Matrix Y Y ℂ) - 1).rank ≤ E.rank := by
    have h := rank_le_activeCoreMatrix_rank W i₀ m hm hpowW
    simpa [E, U, hWi] using h
  have hEpos : 0 < E.rank := hrank.trans_le hretain
  have hcardpos : 0 < Fintype.card S := by
    exact hEpos.trans_le (Matrix.rank_le_card_width E)
  letI : Nonempty (TorsionActiveCore.ActiveCoreIndex W) :=
    Fintype.card_pos_iff.mp hcardpos
  have hpowU : U ^ m = 1 := activeCoreMatrix_pow_eq_one W i₀ m hpowW
  have hmass : (E.rank : ℝ) ≤
      (m : ℝ) ^ 2 * ScaledKazhdanTransport.matMass E := by
    exact rank_le_order_sq_mul_matMass U m hm hpowU
  have hmassEq : ScaledKazhdanTransport.matMass E =
      (Fintype.card S : ℝ) * hsNormSq S E := by
    rw [UltraproductScaledTransport.hsNormSq_eq_matMass_div]
    have hc : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast hcardpos.ne'
    field_simp [hc]
    rfl
  have hrankR : (((R : Matrix Y Y ℂ) - 1).rank : ℝ) ≤
      (m : ℝ) ^ 2 * ((Fintype.card S : ℝ) * hsNormSq S E) := by
    calc
      (((R : Matrix Y Y ℂ) - 1).rank : ℝ) ≤ (E.rank : ℝ) := by
        exact_mod_cast hretain
      _ ≤ (m : ℝ) ^ 2 * ScaledKazhdanTransport.matMass E := hmass
      _ = (m : ℝ) ^ 2 * ((Fintype.card S : ℝ) * hsNormSq S E) := by
        rw [hmassEq]
  have hdimR : (Fintype.card S : ℝ) ≤
      (TorsionActiveCore.totalWordLength words : ℝ) *
        (((R : Matrix Y Y ℂ) - 1).rank : ℝ) := by
    exact_mod_cast hdim
  have hhs : 0 ≤ hsNormSq S E := hsNormSq_nonneg S E
  have hscaled : (((R : Matrix Y Y ℂ) - 1).rank : ℝ) ≤
      (m : ℝ) ^ 2 *
        (((TorsionActiveCore.totalWordLength words : ℝ) *
          (((R : Matrix Y Y ℂ) - 1).rank : ℝ)) * hsNormSq S E) := by
    refine hrankR.trans ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hdimR hhs) (sq_nonneg (m : ℝ))
  refine ⟨hdim, ?_⟩
  have hrankRpos : 0 < (((R : Matrix Y Y ℂ) - 1).rank : ℝ) := by
    exact_mod_cast hrank
  have hmul : (((R : Matrix Y Y ℂ) - 1).rank : ℝ) * 1 ≤
      (((R : Matrix Y Y ℂ) - 1).rank : ℝ) *
        ((m : ℝ) ^ 2 * (TorsionActiveCore.totalWordLength words : ℝ) *
          hsNormSq S E) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hgap : 1 ≤
      (m : ℝ) ^ 2 * (TorsionActiveCore.totalWordLength words : ℝ) *
        hsNormSq S E :=
    le_of_mul_le_mul_left hmul hrankRpos
  change 1 ≤
    (m : ℝ) ^ 2 * (TorsionActiveCore.totalWordLength words : ℝ) *
      hsNormSq S E
  exact hgap

end

end FiniteOrderRankMass
end GroupApproximation
