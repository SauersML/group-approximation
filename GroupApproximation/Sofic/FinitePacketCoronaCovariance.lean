import GroupApproximation.Sofic.FiniteGroupCoronaExactification
import GroupApproximation.Sofic.FinitePacketCovariance

/-!
# Exact finite-packet covariance in a norm-matrix corona

This file joins the two finite-dimensional ingredients of the packet route.
A finite subgroup representation in the norm-matrix corona is first replaced
by exact coordinate representations.  For finitely many normalizing movers,
finite averaging and polar decomposition then correct their chosen unitary
lifts to exact coordinate covariance.  The correction is operator-norm null,
so neither the packet nor the movers change in the corona.

No commutativity of the finite packet is assumed.
-/

namespace GroupApproximation
namespace FinitePacketCoronaCovariance

open Filter Matrix
open FiniteGroupCoronaExactification FinitePacketCovariance
open scoped Topology Matrix.Norms.L2Operator

noncomputable section

universe u v w

variable {F : Type u} [Group F] [Fintype F]
variable {A : Type v} [Fintype A]
variable {X : ℕ → FiniteModel}

noncomputable local instance matrixBlockCStarAlgebra
    (Y : Type) [Fintype Y] [DecidableEq Y] [Nonempty Y] :
    CStarAlgebra (Matrix Y Y ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- Reinterpret matrix-unitary-group representations as C-star-unitary
representations. -/
def matrixUnitaryToCStarHom {Y : FiniteModel} [Nonempty Y] :
    Matrix.unitaryGroup Y ℂ →* unitary (Matrix Y Y ℂ) where
  toFun := matrixUnitaryToCStar
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Conjugating an exact matrix representation by a unitary gives an exact
representation. -/
def conjugatedRepresentation {Y : FiniteModel} [Nonempty Y]
    (U : Matrix.unitaryGroup Y ℂ)
    (V : F →* Matrix.unitaryGroup Y ℂ) :
    F →* unitary (Matrix Y Y ℂ) :=
  matrixUnitaryToCStarHom.comp
    { toFun := fun f ↦ U * V f * U⁻¹
      map_one' := by simp
      map_mul' := by
        intro f g
        simp only [map_mul]
        group }

/-- Relabel an exact packet representation by an automorphism of the packet. -/
def relabeledRepresentation {Y : FiniteModel} [Nonempty Y]
    (β : F ≃* F) (V : F →* Matrix.unitaryGroup Y ℂ) :
    F →* unitary (Matrix Y Y ℂ) :=
  matrixUnitaryToCStarHom.comp (V.comp β.toMonoidHom)

/-- Total pointwise covariance defect for finitely many movers.  It is a sum,
rather than a maximum, so convergence follows directly from finite sums. -/
def totalCovarianceDefect
    (hX : ∀ n, Nonempty (X n))
    (β : A → F ≃* F)
    (V : ∀ n, F →* Matrix.unitaryGroup (X n) ℂ)
    (U : A → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (n : ℕ) : ℝ := by
  letI : Nonempty (X n) := hX n
  exact ∑ a : A, ∑ f : F,
    ‖(((relabeledRepresentation (β a) (V n)) f :
          unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ) -
      (((conjugatedRepresentation (U a n) (V n)) f :
          unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ)‖

theorem totalCovarianceDefect_nonneg
    (hX : ∀ n, Nonempty (X n))
    (β : A → F ≃* F)
    (V : ∀ n, F →* Matrix.unitaryGroup (X n) ℂ)
    (U : A → ∀ n, Matrix.unitaryGroup (X n) ℂ) (n : ℕ) :
    0 ≤ totalCovarianceDefect hX β V U n := by
  unfold totalCovarianceDefect
  positivity

/-- Every covariance coordinate is bounded by the total defect. -/
theorem coordinateCovarianceDefect_le_total
    (hX : ∀ n, Nonempty (X n))
    (β : A → F ≃* F)
    (V : ∀ n, F →* Matrix.unitaryGroup (X n) ℂ)
    (U : A → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (n : ℕ) (a : A) (f : F) :
    ‖(((relabeledRepresentation (β a) (V n)) f :
          unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ) -
      (((conjugatedRepresentation (U a n) (V n)) f :
          unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ)‖ ≤
      totalCovarianceDefect hX β V U n := by
  letI : Nonempty (X n) := hX n
  unfold totalCovarianceDefect
  let d : A → F → ℝ := fun a' f' ↦
    ‖(((relabeledRepresentation (β a') (V n)) f' :
          unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ) -
      (((conjugatedRepresentation (U a' n) (V n)) f' :
          unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ)‖
  have hd : ∀ a' f', 0 ≤ d a' f' := fun _ _ ↦ norm_nonneg _
  change d a f ≤ ∑ a' : A, ∑ f' : F, d a' f'
  calc
    d a f ≤ ∑ f' : F, d a f' :=
      Finset.single_le_sum (fun f' _ ↦ hd a f') (Finset.mem_univ f)
    _ ≤ ∑ a' : A, ∑ f' : F, d a' f' :=
      Finset.single_le_sum
        (fun a' _ ↦ Finset.sum_nonneg fun f' _ ↦ hd a' f')
        (Finset.mem_univ a)

omit [Fintype F] [Fintype A] in
/-- A coordinate covariance relation holding in the corona makes the
corresponding exact-lift defect tend to zero. -/
theorem coordinateCovarianceDefect_tendsto_zero
    (hX : ∀ n, Nonempty (X n))
    (rho : F →* NormMatrixCoronaUnitary X)
    (β : A → F ≃* F)
    (V : ∀ n, F →* Matrix.unitaryGroup (X n) ℂ)
    (hV : ∀ f, QuotientGroup.mk (fun n ↦ V n f) = rho f)
    (U : A → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hcov : ∀ a f,
      QuotientGroup.mk (U a) * rho f * (QuotientGroup.mk (U a))⁻¹ =
        rho (β a f))
    (a : A) (f : F) :
    Tendsto (fun n ↦
      ‖(((relabeledRepresentation (β a) (V n)) f :
            unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ) -
        (((conjugatedRepresentation (U a n) (V n)) f :
            unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ)‖)
      cofinite (𝓝 0) := by
  let phi : ∀ n, Matrix.unitaryGroup (X n) ℂ :=
    fun n ↦ U a n * V n f * (U a n)⁻¹
  let psi : ∀ n, Matrix.unitaryGroup (X n) ℂ :=
    fun n ↦ V n (β a f)
  have heq : (QuotientGroup.mk phi : NormMatrixCoronaUnitary X) =
      QuotientGroup.mk psi := by
    calc
      QuotientGroup.mk phi =
          QuotientGroup.mk (U a) *
            QuotientGroup.mk (fun n ↦ V n f) *
              (QuotientGroup.mk (U a))⁻¹ := by
                change QuotientGroup.mk
                    (U a * (fun n ↦ V n f) * (U a)⁻¹) = _
                rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul,
                  QuotientGroup.mk_inv]
      _ = QuotientGroup.mk (U a) * rho f *
            (QuotientGroup.mk (U a))⁻¹ := by rw [hV f]
      _ = rho (β a f) := hcov a f
      _ = QuotientGroup.mk psi := by
        change rho (β a f) = QuotientGroup.mk (fun n ↦ V n (β a f))
        exact (hV (β a f)).symm
  have hnull : phi⁻¹ * psi ∈ nullCofiniteOpSubgroup X :=
    QuotientGroup.eq.mp heq
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hnull ε hε] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  change ‖(psi n : Matrix (X n) (X n) ℂ) -
      (phi n : Matrix (X n) (X n) ℂ)‖ < ε
  change opLength (X n) ((phi⁻¹ * psi) n) < ε at hn
  simpa only [Pi.mul_apply, Pi.inv_apply, opLength_inv_mul] using hn

/-- All finitely many covariance defects tend to zero simultaneously. -/
theorem totalCovarianceDefect_tendsto_zero
    (hX : ∀ n, Nonempty (X n))
    (rho : F →* NormMatrixCoronaUnitary X)
    (β : A → F ≃* F)
    (V : ∀ n, F →* Matrix.unitaryGroup (X n) ℂ)
    (hV : ∀ f, QuotientGroup.mk (fun n ↦ V n f) = rho f)
    (U : A → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hcov : ∀ a f,
      QuotientGroup.mk (U a) * rho f * (QuotientGroup.mk (U a))⁻¹ =
        rho (β a f)) :
    Tendsto (totalCovarianceDefect hX β V U) cofinite (𝓝 0) := by
  unfold totalCovarianceDefect
  simpa using tendsto_finsetSum Finset.univ fun a _ ↦
    tendsto_finsetSum Finset.univ fun f _ ↦
      coordinateCovarianceDefect_tendsto_zero hX rho β V hV U hcov a f

/-- Right multiplication by a unitary identifies the covariance-product
defect with the pointwise distance. -/
theorem norm_mul_star_sub_one_eq_norm_sub
    {Y : FiniteModel} [Nonempty Y]
    (p q : unitary (Matrix Y Y ℂ)) :
    ‖((p : unitary (Matrix Y Y ℂ)) : Matrix Y Y ℂ) *
          star (((q : unitary (Matrix Y Y ℂ)) : Matrix Y Y ℂ)) - 1‖ =
      ‖((p : unitary (Matrix Y Y ℂ)) : Matrix Y Y ℂ) -
          ((q : unitary (Matrix Y Y ℂ)) : Matrix Y Y ℂ)‖ := by
  have hq : ((q : unitary (Matrix Y Y ℂ)) : Matrix Y Y ℂ) *
      star (((q : unitary (Matrix Y Y ℂ)) : Matrix Y Y ℂ)) = 1 :=
    Unitary.mul_star_self_of_mem q.prop
  have hid : ((p : unitary (Matrix Y Y ℂ)) : Matrix Y Y ℂ) *
        star (((q : unitary (Matrix Y Y ℂ)) : Matrix Y Y ℂ)) - 1 =
      (((p : unitary (Matrix Y Y ℂ)) : Matrix Y Y ℂ) -
        ((q : unitary (Matrix Y Y ℂ)) : Matrix Y Y ℂ)) *
          star (((q : unitary (Matrix Y Y ℂ)) : Matrix Y Y ℂ)) := by
    rw [Matrix.sub_mul, hq]
  rw [hid, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem q.prop)]

/-- The polar correction for one mover, chosen whenever the common total
defect is at most `1/8`. -/
def covarianceCorrection
    (hX : ∀ n, Nonempty (X n))
    (β : A → F ≃* F)
    (V : ∀ n, F →* Matrix.unitaryGroup (X n) ℂ)
    (U : A → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (a : A) (n : ℕ) : unitary (Matrix (X n) (X n) ℂ) := by
  letI : Nonempty (X n) := hX n
  let ε := totalCovarianceDefect hX β V U n
  by_cases hsmall : ε ≤ 1 / 8
  · have hclose : ∀ f : F,
        ‖(((relabeledRepresentation (β a) (V n)) f :
              unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ) *
            star ((((conjugatedRepresentation (U a n) (V n)) f :
              unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ)) - 1‖ ≤ ε := by
      intro f
      rw [norm_mul_star_sub_one_eq_norm_sub]
      exact coordinateCovarianceDefect_le_total hX β V U n a f
    exact Classical.choose (exists_near_identity_exact_covariance
      (conjugatedRepresentation (U a n) (V n))
      (relabeledRepresentation (β a) (V n))
      (totalCovarianceDefect_nonneg hX β V U n) hsmall hclose)
  · exact 1

theorem covarianceCorrection_spec
    (hX : ∀ n, Nonempty (X n))
    (β : A → F ≃* F)
    (V : ∀ n, F →* Matrix.unitaryGroup (X n) ℂ)
    (U : A → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (a : A) (n : ℕ)
    (hsmall : totalCovarianceDefect hX β V U n ≤ 1 / 8) :
    ‖((covarianceCorrection hX β V U a n :
          unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ) - 1‖ ≤
        6 * totalCovarianceDefect hX β V U n ∧
      ∀ f : F,
        ((covarianceCorrection hX β V U a n :
            unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ) *
          (((conjugatedRepresentation (U a n) (V n)) f :
            unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ) *
          star (((covarianceCorrection hX β V U a n :
            unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ)) =
          (((relabeledRepresentation (β a) (V n)) f :
            unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ) := by
  letI : Nonempty (X n) := hX n
  let ε := totalCovarianceDefect hX β V U n
  have hclose : ∀ f : F,
      ‖(((relabeledRepresentation (β a) (V n)) f :
            unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ) *
          star ((((conjugatedRepresentation (U a n) (V n)) f :
            unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ)) - 1‖ ≤ ε := by
    intro f
    rw [norm_mul_star_sub_one_eq_norm_sub]
    exact coordinateCovarianceDefect_le_total hX β V U n a f
  have hspec := Classical.choose_spec (exists_near_identity_exact_covariance
    (conjugatedRepresentation (U a n) (V n))
    (relabeledRepresentation (β a) (V n))
    (totalCovarianceDefect_nonneg hX β V U n) hsmall hclose)
  simpa only [covarianceCorrection, dif_pos hsmall] using hspec

/-- Use the exact packet on good coordinates and the trivial packet elsewhere.
The bad set is finite once the total defect tends to zero. -/
def exactPacketCoordinate
    (hX : ∀ n, Nonempty (X n))
    (β : A → F ≃* F)
    (V : ∀ n, F →* Matrix.unitaryGroup (X n) ℂ)
    (U : A → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (n : ℕ) : F →* Matrix.unitaryGroup (X n) ℂ :=
  if totalCovarianceDefect hX β V U n ≤ 1 / 8 then V n else 1

/-- Correct a mover on good coordinates.  On bad coordinates the packet is
trivial, so the original mover is already exactly covariant. -/
def exactCovariantMover
    (hX : ∀ n, Nonempty (X n))
    (β : A → F ≃* F)
    (V : ∀ n, F →* Matrix.unitaryGroup (X n) ℂ)
    (U : A → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (a : A) (n : ℕ) : Matrix.unitaryGroup (X n) ℂ :=
  if totalCovarianceDefect hX β V U n ≤ 1 / 8 then
    cstarUnitaryToMatrix (covarianceCorrection hX β V U a n) * U a n
  else U a n

/-- The corrected mover implements the prescribed packet automorphism at
every coordinate, including the finitely many discarded coordinates. -/
theorem exactCovariantMover_covariance
    (hX : ∀ n, Nonempty (X n))
    (β : A → F ≃* F)
    (V : ∀ n, F →* Matrix.unitaryGroup (X n) ℂ)
    (U : A → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (n : ℕ) (a : A) (f : F) :
    exactCovariantMover hX β V U a n *
        exactPacketCoordinate hX β V U n f *
          (exactCovariantMover hX β V U a n)⁻¹ =
      exactPacketCoordinate hX β V U n (β a f) := by
  letI : Nonempty (X n) := hX n
  by_cases hsmall : totalCovarianceDefect hX β V U n ≤ 1 / 8
  · have hspec := (covarianceCorrection_spec hX β V U a n hsmall).2 f
    simp only [exactCovariantMover, exactPacketCoordinate, if_pos hsmall]
    let z : Matrix.unitaryGroup (X n) ℂ :=
      cstarUnitaryToMatrix (covarianceCorrection hX β V U a n)
    have hspecUnitary :
        covarianceCorrection hX β V U a n *
              (conjugatedRepresentation (U a n) (V n)) f *
              (covarianceCorrection hX β V U a n)⁻¹ =
            (relabeledRepresentation (β a) (V n)) f := by
      apply Subtype.ext
      exact hspec
    have hspec' : z * (U a n * V n f * (U a n)⁻¹) * z⁻¹ = V n (β a f) := by
      have hmapped := congrArg
        (cstarUnitaryToMatrixHom (Y := X n)) hspecUnitary
      simp only [map_mul, map_inv] at hmapped
      change z * (U a n * V n f * (U a n)⁻¹) * z⁻¹ = V n (β a f)
        at hmapped
      exact hmapped
    calc
      (cstarUnitaryToMatrix (covarianceCorrection hX β V U a n) * U a n) *
            V n f *
          (cstarUnitaryToMatrix (covarianceCorrection hX β V U a n) * U a n)⁻¹ =
          z * (U a n * V n f * (U a n)⁻¹) * z⁻¹ := by
            dsimp [z]
            group
      _ = V n (β a f) := hspec'
  · simp only [exactCovariantMover, exactPacketCoordinate, if_neg hsmall]
    simp

/-- The corrected mover differs from the chosen lift by at most six times the
common total covariance defect. -/
theorem norm_exactCovariantMover_sub_le
    (hX : ∀ n, Nonempty (X n))
    (β : A → F ≃* F)
    (V : ∀ n, F →* Matrix.unitaryGroup (X n) ℂ)
    (U : A → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (a : A) (n : ℕ) :
    ‖(exactCovariantMover hX β V U a n : Matrix (X n) (X n) ℂ) - U a n‖ ≤
      6 * totalCovarianceDefect hX β V U n := by
  letI : Nonempty (X n) := hX n
  by_cases hsmall : totalCovarianceDefect hX β V U n ≤ 1 / 8
  · have hz := (covarianceCorrection_spec hX β V U a n hsmall).1
    simp only [exactCovariantMover, if_pos hsmall]
    change ‖(((covarianceCorrection hX β V U a n :
          unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ) *
        (U a n : Matrix (X n) (X n) ℂ)) -
          (U a n : Matrix (X n) (X n) ℂ)‖ ≤ _
    have hid :
        (((covarianceCorrection hX β V U a n :
            unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ) *
              (U a n : Matrix (X n) (X n) ℂ)) -
            (U a n : Matrix (X n) (X n) ℂ) =
          ((((covarianceCorrection hX β V U a n :
              unitary (Matrix (X n) (X n) ℂ)) : Matrix (X n) (X n) ℂ) - 1) *
            (U a n : Matrix (X n) (X n) ℂ)) := by
      rw [Matrix.sub_mul, one_mul]
    rw [hid, CStarRing.norm_mul_mem_unitary _ (U a n).2]
    exact hz
  · simp only [exactCovariantMover, if_neg hsmall, sub_self, norm_zero]
    exact mul_nonneg (by norm_num) (totalCovarianceDefect_nonneg hX β V U n)

/-- **Closed finite-packet corona covariance bridge.**

For a corona representation of a finite group and finitely many unitary
normalizers implementing specified packet automorphisms, there are exact
same-dimension coordinate packet representations and corrected normalizer
lifts.  They represent the original corona elements and satisfy exact
covariance at every coordinate. -/
theorem exists_exact_covariant_coordinate_lifts
    (hX : ∀ n, Nonempty (X n))
    (rho : F →* NormMatrixCoronaUnitary X)
    (β : A → F ≃* F)
    (U : A → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hcov : ∀ a f,
      QuotientGroup.mk (U a) * rho f * (QuotientGroup.mk (U a))⁻¹ =
        rho (β a f)) :
    ∃ V : ∀ n, F →* Matrix.unitaryGroup (X n) ℂ,
      ∃ Uhat : A → ∀ n, Matrix.unitaryGroup (X n) ℂ,
        (∀ f, QuotientGroup.mk (fun n ↦ V n f) = rho f) ∧
        (∀ a, (QuotientGroup.mk (Uhat a) : NormMatrixCoronaUnitary X) =
          QuotientGroup.mk (U a)) ∧
        (∀ n a f, Uhat a n * V n f * (Uhat a n)⁻¹ = V n (β a f)) := by
  classical
  obtain ⟨V₀, hV₀⟩ :=
    exists_exact_coordinate_lift (F := F) (X := X) hX rho
  let d : ℕ → ℝ := totalCovarianceDefect hX β V₀ U
  have hd : Tendsto d cofinite (𝓝 0) :=
    totalCovarianceDefect_tendsto_zero hX rho β V₀ hV₀ U hcov
  have hsmall : ∀ᶠ n in cofinite, d n ≤ 1 / 8 := by
    have hnhds := (Metric.tendsto_nhds.1 hd) (1 / 8) (by norm_num)
    filter_upwards [hnhds] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg
      (totalCovarianceDefect_nonneg hX β V₀ U n)] at hn
    exact hn.le
  let V : ∀ n, F →* Matrix.unitaryGroup (X n) ℂ :=
    exactPacketCoordinate hX β V₀ U
  let Uhat : A → ∀ n, Matrix.unitaryGroup (X n) ℂ :=
    exactCovariantMover hX β V₀ U
  refine ⟨V, Uhat, ?_, ?_, ?_⟩
  · intro f
    rw [← hV₀ f]
    apply QuotientGroup.eq.mpr
    intro ε hε
    filter_upwards [hsmall] with n hn
    change totalCovarianceDefect hX β V₀ U n ≤ 1 / 8 at hn
    change opLength (X n) ((V n f)⁻¹ * V₀ n f) < ε
    have hVeq : V n f = V₀ n f := by
      simp only [V, exactPacketCoordinate, if_pos hn]
    rw [hVeq, inv_mul_cancel, opLength_one]
    exact hε
  · intro a
    apply QuotientGroup.eq.mpr
    intro ε hε
    have hevent : ∀ᶠ n in cofinite, 6 * d n < ε := by
      have hnear := (Metric.tendsto_nhds.1 hd) (ε / 6) (by positivity)
      filter_upwards [hnear] with n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg
        (totalCovarianceDefect_nonneg hX β V₀ U n)] at hn
      nlinarith
    filter_upwards [hevent] with n hn
    change opLength (X n) ((Uhat a n)⁻¹ * U a n) < ε
    rw [opLength_inv_mul]
    rw [norm_sub_rev]
    exact (norm_exactCovariantMover_sub_le hX β V₀ U a n).trans_lt hn
  · exact exactCovariantMover_covariance hX β V₀ U

/-- **Ambient-group form of finite-packet covariance.**

The packet and its movers now come from an ambient group representation.
The theorem chooses coordinate lifts of every mover itself and derives the
corona covariance relation from the stated group identity.  Thus neither
coordinate packet representations nor coordinate covariance data are caller
inputs. -/
theorem exists_exact_covariant_coordinate_lifts_of_ambient
    {E : Type w} [Group E]
    (hX : ∀ n, Nonempty (X n))
    (rho : E →* NormMatrixCoronaUnitary X)
    (packet : F →* E)
    (mover : A → E)
    (β : A → F ≃* F)
    (hcov : ∀ a f,
      mover a * packet f * (mover a)⁻¹ = packet (β a f)) :
    ∃ V : ∀ n, F →* Matrix.unitaryGroup (X n) ℂ,
      ∃ Uhat : A → ∀ n, Matrix.unitaryGroup (X n) ℂ,
        (∀ f, QuotientGroup.mk (fun n ↦ V n f) = rho (packet f)) ∧
        (∀ a, (QuotientGroup.mk (Uhat a) : NormMatrixCoronaUnitary X) =
          rho (mover a)) ∧
        (∀ n a f, Uhat a n * V n f * (Uhat a n)⁻¹ = V n (β a f)) := by
  classical
  choose U hU using fun a : A ↦ QuotientGroup.mk_surjective (rho (mover a))
  have hcovCorona : ∀ a f,
      QuotientGroup.mk (U a) * (rho.comp packet) f *
          (QuotientGroup.mk (U a))⁻¹ =
        (rho.comp packet) (β a f) := by
    intro a f
    calc
      QuotientGroup.mk (U a) * (rho.comp packet) f *
            (QuotientGroup.mk (U a))⁻¹ =
          rho (mover a) * rho (packet f) * (rho (mover a))⁻¹ := by
            rw [hU a]
            rfl
      _ = rho (mover a * packet f * (mover a)⁻¹) := by
            simp only [map_mul, map_inv]
      _ = rho (packet (β a f)) := congrArg rho (hcov a f)
      _ = (rho.comp packet) (β a f) := rfl
  obtain ⟨V, Uhat, hV, hUhat, hcovhat⟩ :=
    exists_exact_covariant_coordinate_lifts hX (rho.comp packet) β U
      hcovCorona
  refine ⟨V, Uhat, ?_, ?_, hcovhat⟩
  · intro f
    exact hV f
  · intro a
    exact (hUhat a).trans (hU a)

end

end FinitePacketCoronaCovariance
end GroupApproximation
