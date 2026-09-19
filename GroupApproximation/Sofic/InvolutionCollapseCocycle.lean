import GroupApproximation.Sofic.InvolutionCollapseProfile
import GroupApproximation.Kazhdan.UltralimitGaussianBoundedness

/-!
# The almost-cocycle structure of the normalized displacement vectors

The flattened displacement dynamics: conjugation by a group microstate is
an isometry of the flattened space (`adFlat`), and the normalized
displacement vectors satisfy the cocycle identity along it with stagewise
vanishing defect (`eventually_coboundary_defect_small`) — the defect is a
sum of three rank-controlled covariance errors, so its normalized mass
dies even at the rank scale.

Consequences: the displacement identity of the profile (`halmost` for the
ultralimit Gaussian machinery), and the standard-part anchor
`sum_profile_eq_four`: the generators carry total profile exactly four.
Together with `profile_bounded_of_isKazhdanPair` this bounds the whole
profile of the collapse family — Delorme with no cocycle at any stage.
-/

namespace GroupApproximation
namespace InvolutionCollapseCocycle

open Matrix InvolutionOrbitMicrostates InvolutionRankMass
open InvolutionCollapseMetric InvolutionMicrostateTools
open InvolutionCollapseProfile Ultralimit UltralimitGaussian
open KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

/-! ## The flattened adjoint action -/

/-- A Euclidean vector as a matrix, inverse to `flatE`. -/
noncomputable def unflatE {Y : Type*} [Fintype Y]
    (x : EuclideanSpace ℂ (Y × Y)) : Matrix Y Y ℂ :=
  Matrix.of fun i j ↦ (EuclideanSpace.equiv (Y × Y) ℂ) x (i, j)

theorem unflatE_flatE {Y : Type*} [Fintype Y] (X : Matrix Y Y ℂ) :
    unflatE (flatE X) = X := by
  ext i j
  have h := (EuclideanSpace.equiv (Y × Y) ℂ).apply_symm_apply
    (fun p : Y × Y ↦ X p.1 p.2)
  exact congrFun h (i, j)

theorem unflatE_real_smul {Y : Type*} [Fintype Y] (r : ℝ)
    (x : EuclideanSpace ℂ (Y × Y)) :
    unflatE (r • x) = r • unflatE x := by
  ext i j
  show (EuclideanSpace.equiv (Y × Y) ℂ) (r • x) (i, j) =
    r • (EuclideanSpace.equiv (Y × Y) ℂ) x (i, j)
  rfl

/-- The flattened adjoint action of a matrix. -/
noncomputable def adFlat {Y : Type*} [Fintype Y] (U : Matrix Y Y ℂ)
    (x : EuclideanSpace ℂ (Y × Y)) : EuclideanSpace ℂ (Y × Y) :=
  flatE (U * unflatE x * Uᴴ)

theorem adFlat_flatE {Y : Type*} [Fintype Y] (U M : Matrix Y Y ℂ) :
    adFlat U (flatE M) = flatE (U * M * Uᴴ) := by
  rw [adFlat, unflatE_flatE]

theorem adFlat_real_smul {Y : Type*} [Fintype Y] (U : Matrix Y Y ℂ)
    (r : ℝ) (x : EuclideanSpace ℂ (Y × Y)) :
    adFlat U (r • x) = r • adFlat U x := by
  unfold adFlat
  rw [unflatE_real_smul]
  have hmat : U * (r • unflatE x) * Uᴴ = r • (U * unflatE x * Uᴴ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hmat]
  ext p
  show (EuclideanSpace.equiv (Y × Y) ℂ).symm
      (fun q ↦ (r • (U * unflatE x * Uᴴ)) q.1 q.2) p =
    (r • (EuclideanSpace.equiv (Y × Y) ℂ).symm
      (fun q ↦ (U * unflatE x * Uᴴ) q.1 q.2)) p
  rfl

theorem adFlat_sub {Y : Type*} [Fintype Y] (U : Matrix Y Y ℂ)
    (x y : EuclideanSpace ℂ (Y × Y)) :
    adFlat U (x - y) = adFlat U x - adFlat U y := by
  unfold adFlat
  have hunflat : unflatE (x - y) = unflatE x - unflatE y := by
    ext i j
    rfl
  rw [hunflat]
  have hmat : U * (unflatE x - unflatE y) * Uᴴ =
      U * unflatE x * Uᴴ - U * unflatE y * Uᴴ := by
    noncomm_ring
  rw [hmat, flatE_sub]

theorem norm_adFlat {Y : Type*} [Fintype Y] [DecidableEq Y]
    {U : Matrix Y Y ℂ} (hU : U ∈ Matrix.unitaryGroup Y ℂ)
    (x : EuclideanSpace ℂ (Y × Y)) : ‖adFlat U x‖ = ‖x‖ := by
  have hxflat : x = flatE (unflatE x) := by
    ext p
    show x p = (EuclideanSpace.equiv (Y × Y) ℂ).symm
      (fun q ↦ (Matrix.of fun i j ↦
        (EuclideanSpace.equiv (Y × Y) ℂ) x (i, j)) q.1 q.2) p
    rfl
  have hsq : ‖adFlat U x‖ ^ 2 = ‖x‖ ^ 2 := by
    calc
      ‖adFlat U x‖ ^ 2 =
          ScaledKazhdanTransport.matMass (U * unflatE x * Uᴴ) :=
        norm_flatE_sq _
      _ = ScaledKazhdanTransport.matMass (unflatE x) :=
        ScaledKazhdanTransport.matMass_unitary_conj hU _
      _ = ‖flatE (unflatE x)‖ ^ 2 := (norm_flatE_sq _).symm
      _ = ‖x‖ ^ 2 := by rw [← hxflat]
  calc
    ‖adFlat U x‖ = Real.sqrt (‖adFlat U x‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖x‖ ^ 2) := by rw [hsq]
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

/-! ## The standard-part comparison helper -/

/-- Bounded sequences with vanishing difference have equal standard
parts. -/
theorem stdPart_ofSeq_eq_of_vanishing {x y : ℕ → ℝ} {C : ℝ}
    (hx : ∀ n, |x n| ≤ C) (hy : ∀ n, |y n| ≤ C)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, |x n - y n| ≤ ε) :
    ArchimedeanClass.stdPart (Hyperreal.ofSeq x) =
      ArchimedeanClass.stdPart (Hyperreal.ofSeq y) := by
  have hxf : 0 ≤ ArchimedeanClass.mk (Hyperreal.ofSeq x) :=
    ofSeq_finite_of_bounds (fun n ↦ abs_le.mp (hx n) |>.1)
      (fun n ↦ abs_le.mp (hx n) |>.2)
  have hyf : 0 ≤ ArchimedeanClass.mk (Hyperreal.ofSeq y) :=
    ofSeq_finite_of_bounds (fun n ↦ abs_le.mp (hy n) |>.1)
      (fun n ↦ abs_le.mp (hy n) |>.2)
  have hkey : ∀ ε : ℝ, 0 < ε →
      ArchimedeanClass.stdPart (Hyperreal.ofSeq x) ≤
        ArchimedeanClass.stdPart (Hyperreal.ofSeq y) + ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hsub ε hε
    have hyε : Hyperreal.ofSeq (fun n ↦ y n + ε) =
        Hyperreal.ofSeq y + (ε : Hyperreal) := by
      rw [show ((ε : ℝ) : Hyperreal) =
        Hyperreal.ofSeq (fun _ : ℕ ↦ ε) from rfl, ← ofSeq_add]
    have hle : Hyperreal.ofSeq x ≤ Hyperreal.ofSeq (fun n ↦ y n + ε) := by
      rw [Hyperreal.ofSeq_le_ofSeq]
      have hcof : ∀ᶠ n in Filter.cofinite, x n ≤ y n + ε := by
        rw [Filter.eventually_cofinite]
        refine Set.Finite.subset (Set.finite_Iio N) ?_
        intro n hn
        rw [Set.mem_Iio]
        by_contra hlt
        push Not at hlt
        apply hn
        have := abs_le.mp (hN n hlt) |>.1
        linarith [abs_le.mp (hN n hlt) |>.2]
      exact hcof.filter_mono (Filter.hyperfilter_le_cofinite)
    have hyεf : 0 ≤ ArchimedeanClass.mk
        (Hyperreal.ofSeq (fun n ↦ y n + ε)) :=
      ofSeq_finite_of_bounds
        (fun n ↦ (by linarith [abs_le.mp (hy n) |>.1] :
          -(C + ε) ≤ y n + ε))
        (fun n ↦ (by linarith [abs_le.mp (hy n) |>.2] :
          y n + ε ≤ C + ε))
    have hmono := stdPart_mono hxf hyεf hle
    have hsplit : ArchimedeanClass.stdPart
        (Hyperreal.ofSeq (fun n ↦ y n + ε)) =
        ArchimedeanClass.stdPart (Hyperreal.ofSeq y) + ε := by
      rw [hyε, ArchimedeanClass.stdPart_add hyf (KazhdanFiniteModel.hyperreal_coe_finite ε),
        stdPart_coe]
    rw [hsplit] at hmono
    exact hmono
  have hkey' : ∀ ε : ℝ, 0 < ε →
      ArchimedeanClass.stdPart (Hyperreal.ofSeq y) ≤
        ArchimedeanClass.stdPart (Hyperreal.ofSeq x) + ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hsub ε hε
    have hyε : Hyperreal.ofSeq (fun n ↦ x n + ε) =
        Hyperreal.ofSeq x + (ε : Hyperreal) := by
      rw [show ((ε : ℝ) : Hyperreal) =
        Hyperreal.ofSeq (fun _ : ℕ ↦ ε) from rfl, ← ofSeq_add]
    have hle : Hyperreal.ofSeq y ≤ Hyperreal.ofSeq (fun n ↦ x n + ε) := by
      rw [Hyperreal.ofSeq_le_ofSeq]
      have hcof : ∀ᶠ n in Filter.cofinite, y n ≤ x n + ε := by
        rw [Filter.eventually_cofinite]
        refine Set.Finite.subset (Set.finite_Iio N) ?_
        intro n hn
        rw [Set.mem_Iio]
        by_contra hlt
        push Not at hlt
        apply hn
        have := abs_le.mp (hN n hlt) |>.1
        linarith
      exact hcof.filter_mono (Filter.hyperfilter_le_cofinite)
    have hxεf : 0 ≤ ArchimedeanClass.mk
        (Hyperreal.ofSeq (fun n ↦ x n + ε)) :=
      ofSeq_finite_of_bounds
        (fun n ↦ (by linarith [abs_le.mp (hx n) |>.1] :
          -(C + ε) ≤ x n + ε))
        (fun n ↦ (by linarith [abs_le.mp (hx n) |>.2] :
          x n + ε ≤ C + ε))
    have hmono := stdPart_mono hyf hxεf hle
    have hsplit : ArchimedeanClass.stdPart
        (Hyperreal.ofSeq (fun n ↦ x n + ε)) =
        ArchimedeanClass.stdPart (Hyperreal.ofSeq x) + ε := by
      rw [hyε, ArchimedeanClass.stdPart_add hxf (KazhdanFiniteModel.hyperreal_coe_finite ε),
        stdPart_coe]
    rw [hsplit] at hmono
    exact hmono
  have h1 : ArchimedeanClass.stdPart (Hyperreal.ofSeq x) ≤
      ArchimedeanClass.stdPart (Hyperreal.ofSeq y) :=
    le_of_forall_pos_le_add hkey
  have h2 : ArchimedeanClass.stdPart (Hyperreal.ofSeq y) ≤
      ArchimedeanClass.stdPart (Hyperreal.ofSeq x) :=
    le_of_forall_pos_le_add hkey'
  linarith

/-- **Limiting squared seminorms depend only on the eventual values of
bounded sequences.**  Two bounded sequences that agree at all large stages
have the same `Ultralimit.seqNormSq`, because the hyperfilter refines the
cofinite filter.

Nothing here is specific to the collapse: it is a statement about
`Ultralimit.seqNormSq` and `Ultralimit.IsBoundedSeq` alone.  It sits in this
file rather than in `Kazhdan/UltralimitGeometry.lean` only because its proof
runs through `stdPart_ofSeq_eq_of_vanishing` directly above, which is where
the standard-part comparison lives. -/
theorem seqNormSq_congr_of_eventually_eq {H : ℕ → Type*}
    [∀ n, NormedAddCommGroup (H n)] {x y : ∀ n, H n}
    (hx : IsBoundedSeq x) (hy : IsBoundedSeq y)
    (heq : ∃ N, ∀ n ≥ N, x n = y n) :
    seqNormSq x = seqNormSq y := by
  obtain ⟨Cx, hCx⟩ := id hx
  obtain ⟨Cy, hCy⟩ := id hy
  obtain ⟨N₀, hN₀⟩ := heq
  have hCxnn : 0 ≤ Cx := le_trans (norm_nonneg (x 0)) (hCx 0)
  have hCynn : 0 ≤ Cy := le_trans (norm_nonneg (y 0)) (hCy 0)
  rw [seqNormSq_def, seqNormSq_def]
  refine stdPart_ofSeq_eq_of_vanishing
    (C := Cx ^ 2 + Cy ^ 2) ?_ ?_ ?_
  · intro n
    rw [abs_of_nonneg (sq_nonneg _)]
    have := hCx n
    nlinarith [norm_nonneg (x n), sq_nonneg Cy]
  · intro n
    rw [abs_of_nonneg (sq_nonneg _)]
    have := hCy n
    nlinarith [norm_nonneg (y n), sq_nonneg Cx]
  · intro ε hε
    exact ⟨N₀, fun n hn ↦ by
      rw [hN₀ n hn, sub_self, abs_zero]
      exact hε.le⟩

/-! ## The stagewise cocycle defect -/

attribute [local instance] InnerProductSpace.complexToReal

variable {Γ E : Type} [Group Γ] [Group E]
variable (B : OpAlmostRepresentation E)
variable (iota : Γ →* E)
variable (k : E)
variable (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ)
variable (S : Finset Γ)

/-- **The coboundary defect vanishes stagewise.**  The normalized
displacement vectors satisfy the cocycle identity along the flattened
adjoint action up to a defect `D`, and the two factors of
`matMass D ≤ D.rank * ‖D‖ ^ 2` come from two different groupings of
that one defect.  Grouped as three displacements of the commuting
family --- at `γ`, at `μ = a⁻¹ * γ` conjugated, and at `a` --- rank
subadditivity bounds `D.rank` by `Cn * kNorm`.  Grouped as two
covariance errors it has vanishing operator norm.  Neither grouping
implies the other: two exact involutions at small operator distance
can differ in full rank, so the covariance errors are *not* themselves
rank-controlled. -/
theorem eventually_coboundary_defect_small
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n)
    (a γ : Γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N,
      ‖bVec B V S hgen hsymm n γ -
        (adFlat (B.map n (iota a) : Matrix (B.model n) (B.model n) ℂ)
            (bVec B V S hgen hsymm n (a⁻¹ * γ)) +
          bVec B V S hgen hsymm n a)‖ ≤ ε := by
  classical
  set μ : Γ := a⁻¹ * γ with hμ
  set Cn : ℕ := wordLen S hgen hsymm γ + wordLen S hgen hsymm μ +
    wordLen S hgen hsymm a with hCn
  set η : ℝ := ε / (2 * (Real.sqrt Cn + 1)) with hη
  have hηpos : 0 < η := by
    have : (0 : ℝ) < 2 * (Real.sqrt Cn + 1) := by positivity
    exact div_pos hε this
  obtain ⟨N₀, hN₀⟩ := hmark
  obtain ⟨N₁, hN₁⟩ := eventually_dV_le_wordLen_mul_kNorm B iota k V S
    hgen hsymm hVinv hVcomm hVconv γ
  obtain ⟨N₂, hN₂⟩ := eventually_dV_le_wordLen_mul_kNorm B iota k V S
    hgen hsymm hVinv hVcomm hVconv μ
  obtain ⟨N₃, hN₃⟩ := eventually_dV_le_wordLen_mul_kNorm B iota k V S
    hgen hsymm hVinv hVcomm hVconv a
  obtain ⟨N₄, hN₄⟩ := V_covariance_vanishing B iota k V hVconv a μ η hηpos
  obtain ⟨N₅, hN₅⟩ := V_covariance_vanishing B iota k V hVconv a 1 η hηpos
  refine ⟨max (max N₀ N₁) (max (max N₂ N₃) (max N₄ N₅)), fun n hn ↦ ?_⟩
  have hn₀ : n ≥ N₀ := le_trans (le_trans (le_max_left _ _)
    (le_max_left _ _)) hn
  have hn₁ : n ≥ N₁ := le_trans (le_trans (le_max_right _ _)
    (le_max_left _ _)) hn
  have hn₂ : n ≥ N₂ := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _))) hn
  have hn₃ : n ≥ N₃ := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _))) hn
  have hn₄ : n ≥ N₄ := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hn
  have hn₅ : n ≥ N₅ := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hn
  have hk1 : 1 ≤ kNorm B V S n := hN₀ n hn₀
  have hk : 0 < kNorm B V S n := hk1
  have hkR : (1 : ℝ) ≤ (kNorm B V S n : ℝ) := by exact_mod_cast hk1
  have hkRpos : (0 : ℝ) < (kNorm B V S n : ℝ) := by linarith
  have capγ := hN₁ n hn₁
  have capμ := hN₂ n hn₂
  have capa := hN₃ n hn₃
  set U : Matrix (B.model n) (B.model n) ℂ :=
    (B.map n (iota a) : Matrix (B.model n) (B.model n) ℂ) with hU
  have hUmem : U ∈ Matrix.unitaryGroup (B.model n) ℂ :=
    (B.map n (iota a)).2
  set r : ℝ := (Real.sqrt (kNorm B V S n))⁻¹ with hr
  have hrpos : 0 < r := by
    rw [hr]
    have := Real.sqrt_pos.mpr hkRpos
    positivity
  -- in-branch values
  have hbγ : bVec B V S hgen hsymm n γ = r • flatE (V n γ - V n 1) := by
    unfold bVec
    rw [if_pos ⟨hk, capγ⟩]
  have hbμ : bVec B V S hgen hsymm n μ = r • flatE (V n μ - V n 1) := by
    unfold bVec
    rw [if_pos ⟨hk, capμ⟩]
  have hba : bVec B V S hgen hsymm n a = r • flatE (V n a - V n 1) := by
    unfold bVec
    rw [if_pos ⟨hk, capa⟩]
  set M : Matrix (B.model n) (B.model n) ℂ :=
    (V n γ - V n 1) - U * (V n μ - V n 1) * Uᴴ - (V n a - V n 1) with hM
  have hdefect : bVec B V S hgen hsymm n γ -
      (adFlat U (bVec B V S hgen hsymm n μ) +
        bVec B V S hgen hsymm n a) = r • flatE M := by
    have hMflat : flatE M = flatE (V n γ - V n 1) -
        flatE (U * (V n μ - V n 1) * Uᴴ) - flatE (V n a - V n 1) := by
      rw [hM, flatE_sub, flatE_sub]
    rw [hbγ, hbμ, hba, adFlat_real_smul, adFlat_flatE, hMflat,
      smul_sub, smul_sub, sub_add_eq_sub_sub]
  -- the defect is a sum of two covariance errors
  have hMsplit : M = (V n γ - U * V n μ * Uᴴ) +
      (U * V n 1 * Uᴴ - V n a) := by
    rw [hM]
    noncomm_ring
  have hcov₁ : ‖V n γ - U * V n μ * Uᴴ‖ ≤ η := by
    have h := hN₄ n hn₄
    have hrw : a * μ = γ := by
      rw [hμ]
      group
    rw [hrw] at h
    rw [norm_sub_rev] at h
    exact h
  have hcov₂ : ‖U * V n 1 * Uᴴ - V n a‖ ≤ η := by
    have h := hN₅ n hn₅
    have hrw : a * (1 : Γ) = a := mul_one a
    rw [hrw] at h
    exact h
  have hMop : ‖M‖ ≤ 2 * η := by
    rw [hMsplit]
    calc
      ‖(V n γ - U * V n μ * Uᴴ) + (U * V n 1 * Uᴴ - V n a)‖ ≤
          ‖V n γ - U * V n μ * Uᴴ‖ + ‖U * V n 1 * Uᴴ - V n a‖ :=
        norm_add_le _ _
      _ ≤ 2 * η := by linarith
  -- the defect is rank-controlled
  have hconjrank : (U * (V n μ - V n 1) * Uᴴ).rank = (V n μ - V n 1).rank :=
    rank_unitary_conj hUmem _
  have hrankN : M.rank ≤ dV B V n γ 1 + dV B V n μ 1 + dV B V n a 1 := by
    have heq : M = ((V n γ - V n 1) + -(U * (V n μ - V n 1) * Uᴴ)) +
        -(V n a - V n 1) := by
      rw [hM]
      abel
    have h1 : M.rank ≤ ((V n γ - V n 1) +
        -(U * (V n μ - V n 1) * Uᴴ)).rank + (-(V n a - V n 1)).rank := by
      rw [heq]
      exact InvolutionRankMass.rank_add_le _ _
    have h2 : ((V n γ - V n 1) + -(U * (V n μ - V n 1) * Uᴴ)).rank ≤
        (V n γ - V n 1).rank + (V n μ - V n 1).rank := by
      refine le_trans (InvolutionRankMass.rank_add_le _ _) ?_
      rw [InvolutionCollapseMetric.rank_neg, hconjrank]
    rw [InvolutionCollapseMetric.rank_neg] at h1
    exact le_trans h1 (Nat.add_le_add_right h2 _)
  have hrank : (M.rank : ℝ) ≤ (Cn : ℝ) * (kNorm B V S n : ℝ) := by
    have hsum : M.rank ≤ Cn * kNorm B V S n := by
      refine le_trans hrankN ?_
      rw [hCn]
      calc
        dV B V n γ 1 + dV B V n μ 1 + dV B V n a 1 ≤
            wordLen S hgen hsymm γ * kNorm B V S n +
              wordLen S hgen hsymm μ * kNorm B V S n +
              wordLen S hgen hsymm a * kNorm B V S n :=
          Nat.add_le_add (Nat.add_le_add capγ capμ) capa
        _ = (wordLen S hgen hsymm γ + wordLen S hgen hsymm μ +
              wordLen S hgen hsymm a) * kNorm B V S n := by ring
    exact_mod_cast hsum
  -- the mass of the defect
  have hM2 : ‖M‖ ^ 2 ≤ (2 * η) ^ 2 := by
    nlinarith [norm_nonneg M, hMop, hηpos.le]
  have hmass : ScaledKazhdanTransport.matMass M ≤
      ((Cn : ℝ) * (kNorm B V S n : ℝ)) * (2 * η) ^ 2 := by
    calc
      ScaledKazhdanTransport.matMass M ≤ (M.rank : ℝ) * ‖M‖ ^ 2 :=
        matMass_le_rank_mul_sq_opNorm M
      _ ≤ ((Cn : ℝ) * (kNorm B V S n : ℝ)) * (2 * η) ^ 2 :=
        mul_le_mul hrank hM2 (sq_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  -- assemble
  rw [hdefect]
  have hr2 : r ^ 2 = ((kNorm B V S n : ℝ))⁻¹ := by
    rw [hr, inv_pow, Real.sq_sqrt hkRpos.le]
  have hnormsq : ‖r • flatE M‖ ^ 2 ≤ (Cn : ℝ) * (2 * η) ^ 2 := by
    have hns : ‖r • flatE M‖ ^ 2 = r ^ 2 * ‖flatE M‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [hns, norm_flatE_sq, hr2]
    have hks : ((kNorm B V S n : ℝ))⁻¹ *
        (((Cn : ℝ) * (kNorm B V S n : ℝ)) * (2 * η) ^ 2) =
        (Cn : ℝ) * (2 * η) ^ 2 := by
      field_simp
    calc
      ((kNorm B V S n : ℝ))⁻¹ * ScaledKazhdanTransport.matMass M ≤
          ((kNorm B V S n : ℝ))⁻¹ *
            (((Cn : ℝ) * (kNorm B V S n : ℝ)) * (2 * η) ^ 2) := by
        have hinv : (0 : ℝ) ≤ ((kNorm B V S n : ℝ))⁻¹ := by positivity
        exact mul_le_mul_of_nonneg_left hmass hinv
      _ = (Cn : ℝ) * (2 * η) ^ 2 := hks
  have hs : Real.sqrt (Cn : ℝ) ^ 2 = (Cn : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hsn : (0 : ℝ) ≤ Real.sqrt (Cn : ℝ) := Real.sqrt_nonneg _
  have hden : (0 : ℝ) < 2 * (Real.sqrt (Cn : ℝ) + 1) := by positivity
  have h2η : (2 * η) ^ 2 * (Real.sqrt (Cn : ℝ) + 1) ^ 2 = ε ^ 2 := by
    rw [hη]
    field_simp
  have hkey : (Cn : ℝ) ≤ (Real.sqrt (Cn : ℝ) + 1) ^ 2 := by
    nlinarith [hs, hsn]
  have hηbound : (Cn : ℝ) * (2 * η) ^ 2 ≤ ε ^ 2 := by
    calc
      (Cn : ℝ) * (2 * η) ^ 2 ≤
          (Real.sqrt (Cn : ℝ) + 1) ^ 2 * (2 * η) ^ 2 :=
        mul_le_mul_of_nonneg_right hkey (sq_nonneg _)
      _ = ε ^ 2 := by rw [← h2η]; ring
  have hfinal : ‖r • flatE M‖ ^ 2 ≤ ε ^ 2 := hnormsq.trans hηbound
  nlinarith [hfinal, norm_nonneg (r • flatE M), hε.le]

/-! ## Standard parts of finite sums -/

/-- Standard parts distribute over finite sums of uniformly bounded
sequences. -/
theorem stdPart_ofSeq_finset_sum {ι : Type*} (F : Finset ι)
    (x : ι → ℕ → ℝ) (Cb : ι → ℝ)
    (hb : ∀ i ∈ F, ∀ n, |x i n| ≤ Cb i) :
    ArchimedeanClass.stdPart (Hyperreal.ofSeq (fun n ↦ ∑ i ∈ F, x i n)) =
      ∑ i ∈ F, ArchimedeanClass.stdPart (Hyperreal.ofSeq (x i)) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      have hz : (fun n : ℕ ↦ ∑ i ∈ (∅ : Finset ι), x i n) =
          fun _ : ℕ ↦ (0 : ℝ) := by
        funext n
        rw [Finset.sum_empty]
      rw [hz, show Hyperreal.ofSeq (fun _ : ℕ ↦ (0 : ℝ)) =
        ((0 : ℝ) : Hyperreal) from rfl, stdPart_coe, Finset.sum_empty]
  | @insert i F hi ih =>
      have hsplit : Hyperreal.ofSeq (fun n ↦ ∑ j ∈ insert i F, x j n) =
          Hyperreal.ofSeq (x i) +
            Hyperreal.ofSeq (fun n ↦ ∑ j ∈ F, x j n) := by
        rw [← ofSeq_add]
        congr 1
        funext n
        rw [Finset.sum_insert hi]
      have hfin_i : 0 ≤ ArchimedeanClass.mk (Hyperreal.ofSeq (x i)) :=
        ofSeq_finite_of_bounds
          (fun n ↦ abs_le.mp (hb i (Finset.mem_insert_self i F) n) |>.1)
          (fun n ↦ abs_le.mp (hb i (Finset.mem_insert_self i F) n) |>.2)
      have hbF : ∀ n, |∑ j ∈ F, x j n| ≤ ∑ j ∈ F, Cb j := by
        intro n
        calc
          |∑ j ∈ F, x j n| ≤ ∑ j ∈ F, |x j n| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ F, Cb j :=
            Finset.sum_le_sum fun j hj ↦
              hb j (Finset.mem_insert_of_mem hj) n
      have hfin_F : 0 ≤ ArchimedeanClass.mk
          (Hyperreal.ofSeq (fun n ↦ ∑ j ∈ F, x j n)) :=
        ofSeq_finite_of_bounds
          (fun n ↦ abs_le.mp (hbF n) |>.1)
          (fun n ↦ abs_le.mp (hbF n) |>.2)
      rw [hsplit, ArchimedeanClass.stdPart_add hfin_i hfin_F,
        ih (fun j hj ↦ hb j (Finset.mem_insert_of_mem hj)),
        Finset.sum_insert hi]

/-! ## The anchor and the displacement identity -/

/-- **The profile anchor**: the generators carry total limiting squared
mass exactly four. -/
theorem sum_seqNormSq_bVec_eq_four
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n) :
    ∑ a ∈ S, seqNormSq (fun n ↦ bVec B V S hgen hsymm n a) = 4 := by
  classical
  have hbound : ∀ a ∈ S, ∀ n,
      |‖bVec B V S hgen hsymm n a‖ ^ 2| ≤
        4 * (wordLen S hgen hsymm a : ℝ) := by
    intro a _ n
    rw [abs_of_nonneg (sq_nonneg _)]
    exact norm_bVec_sq_le B V S hgen hsymm hVinv hVcomm n a
  calc
    ∑ a ∈ S, seqNormSq (fun n ↦ bVec B V S hgen hsymm n a) =
        ∑ a ∈ S, ArchimedeanClass.stdPart
          (Hyperreal.ofSeq fun n ↦ ‖bVec B V S hgen hsymm n a‖ ^ 2) := by
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [seqNormSq_def]
    _ = ArchimedeanClass.stdPart (Hyperreal.ofSeq fun n ↦
        ∑ a ∈ S, ‖bVec B V S hgen hsymm n a‖ ^ 2) :=
      (stdPart_ofSeq_finset_sum S _
        (fun a ↦ 4 * (wordLen S hgen hsymm a : ℝ)) hbound).symm
    _ = 4 := by
      obtain ⟨N₀, hN₀⟩ := hmark
      have hveq := stdPart_ofSeq_eq_of_vanishing
        (x := fun n ↦ ∑ a ∈ S, ‖bVec B V S hgen hsymm n a‖ ^ 2)
        (y := fun _ ↦ (4 : ℝ))
        (C := (∑ a ∈ S, 4 * (wordLen S hgen hsymm a : ℝ)) + 4)
        (fun n ↦ by
          have h1 : |∑ a ∈ S, ‖bVec B V S hgen hsymm n a‖ ^ 2| ≤
              ∑ a ∈ S, 4 * (wordLen S hgen hsymm a : ℝ) := by
            calc
              |∑ a ∈ S, ‖bVec B V S hgen hsymm n a‖ ^ 2| ≤
                  ∑ a ∈ S, |‖bVec B V S hgen hsymm n a‖ ^ 2| :=
                Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ a ∈ S, 4 * (wordLen S hgen hsymm a : ℝ) :=
                Finset.sum_le_sum fun a ha ↦ hbound a ha n
          have h2 : (0 : ℝ) ≤ 4 := by norm_num
          calc
            |∑ a ∈ S, ‖bVec B V S hgen hsymm n a‖ ^ 2| ≤
                ∑ a ∈ S, 4 * (wordLen S hgen hsymm a : ℝ) := h1
            _ ≤ (∑ a ∈ S, 4 * (wordLen S hgen hsymm a : ℝ)) + 4 := by
              linarith)
        (fun _ ↦ by
          have hsum : (0 : ℝ) ≤
              ∑ a ∈ S, 4 * (wordLen S hgen hsymm a : ℝ) :=
            Finset.sum_nonneg fun a _ ↦ by positivity
          rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
          linarith)
        (fun ε hε ↦ ⟨N₀, fun n hn ↦ by
          rw [sum_normSq_bVec_eq_four B V S hgen hsymm hVinv hVcomm
            (hN₀ n hn), sub_self, abs_zero]
          exact hε.le⟩)
      rw [hveq]
      rw [show Hyperreal.ofSeq (fun _ : ℕ ↦ (4 : ℝ)) =
        ((4 : ℝ) : Hyperreal) from rfl, stdPart_coe]

/-- **The displacement identity** (`halmost`): the limiting squared norm
of a quotient displacement equals that of the difference — the input the
ultralimit Gaussian machinery needs. -/
theorem profile_halmost
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n)
    (g h : Γ) :
    ArchimedeanClass.stdPart (Hyperreal.ofSeq fun n ↦
        ‖bVec B V S hgen hsymm n (g⁻¹ * h)‖ ^ 2) =
      ArchimedeanClass.stdPart (Hyperreal.ofSeq fun n ↦
        ‖bVec B V S hgen hsymm n h - bVec B V S hgen hsymm n g‖ ^ 2) := by
  classical
  set sh : ℝ := Real.sqrt (4 * (wordLen S hgen hsymm h : ℝ)) with hsh
  set sg : ℝ := Real.sqrt (4 * (wordLen S hgen hsymm g : ℝ)) with hsg
  set sμ : ℝ :=
    Real.sqrt (4 * (wordLen S hgen hsymm (g⁻¹ * h) : ℝ)) with hsμ
  have hnormh : ∀ n, ‖bVec B V S hgen hsymm n h‖ ≤ sh := by
    intro n
    rw [hsh]
    have := norm_bVec_sq_le B V S hgen hsymm hVinv hVcomm n h
    have hnn := norm_nonneg (bVec B V S hgen hsymm n h)
    nlinarith [Real.sq_sqrt (by positivity :
        (0 : ℝ) ≤ 4 * (wordLen S hgen hsymm h : ℝ)),
      Real.sqrt_nonneg (4 * (wordLen S hgen hsymm h : ℝ))]
  have hnormg : ∀ n, ‖bVec B V S hgen hsymm n g‖ ≤ sg := by
    intro n
    rw [hsg]
    have := norm_bVec_sq_le B V S hgen hsymm hVinv hVcomm n g
    have hnn := norm_nonneg (bVec B V S hgen hsymm n g)
    nlinarith [Real.sq_sqrt (by positivity :
        (0 : ℝ) ≤ 4 * (wordLen S hgen hsymm g : ℝ)),
      Real.sqrt_nonneg (4 * (wordLen S hgen hsymm g : ℝ))]
  have hnormμ : ∀ n, ‖bVec B V S hgen hsymm n (g⁻¹ * h)‖ ≤ sμ := by
    intro n
    rw [hsμ]
    have := norm_bVec_sq_le B V S hgen hsymm hVinv hVcomm n (g⁻¹ * h)
    have hnn := norm_nonneg (bVec B V S hgen hsymm n (g⁻¹ * h))
    nlinarith [Real.sq_sqrt (by positivity :
        (0 : ℝ) ≤ 4 * (wordLen S hgen hsymm (g⁻¹ * h) : ℝ)),
      Real.sqrt_nonneg (4 * (wordLen S hgen hsymm (g⁻¹ * h) : ℝ))]
  have hshn : 0 ≤ sh := Real.sqrt_nonneg _
  have hsgn : 0 ≤ sg := Real.sqrt_nonneg _
  have hsμn : 0 ≤ sμ := Real.sqrt_nonneg _
  set Ctot : ℝ := (sh + sg) + sμ + 1 with hCtot
  have hCtotpos : 0 < Ctot := by rw [hCtot]; linarith
  refine stdPart_ofSeq_eq_of_vanishing
    (C := (sμ ^ 2) + ((sh + sg) ^ 2) + 1) ?_ ?_ ?_
  · intro n
    rw [abs_of_nonneg (sq_nonneg _)]
    have h1 := hnormμ n
    have hnn := norm_nonneg (bVec B V S hgen hsymm n (g⁻¹ * h))
    nlinarith [sq_nonneg (sh + sg)]
  · intro n
    rw [abs_of_nonneg (sq_nonneg _)]
    have hd : ‖bVec B V S hgen hsymm n h - bVec B V S hgen hsymm n g‖ ≤
        sh + sg := by
      calc
        ‖bVec B V S hgen hsymm n h - bVec B V S hgen hsymm n g‖ ≤
            ‖bVec B V S hgen hsymm n h‖ + ‖bVec B V S hgen hsymm n g‖ :=
          norm_sub_le _ _
        _ ≤ sh + sg := add_le_add (hnormh n) (hnormg n)
    have hnn := norm_nonneg
      (bVec B V S hgen hsymm n h - bVec B V S hgen hsymm n g)
    nlinarith [sq_nonneg sμ]
  · intro ε hε
    have hε' : 0 < ε / (2 * Ctot) := by positivity
    obtain ⟨N, hN⟩ := eventually_coboundary_defect_small B iota k V S
      hgen hsymm hVinv hVcomm hVconv hmark g h hε'
    refine ⟨N, fun n hn ↦ ?_⟩
    have hdef := hN n hn
    set w₁ : EuclideanSpace ℂ (B.model n × B.model n) :=
      adFlat (B.map n (iota g) : Matrix (B.model n) (B.model n) ℂ)
        (bVec B V S hgen hsymm n (g⁻¹ * h)) with hw₁
    set w₂ : EuclideanSpace ℂ (B.model n × B.model n) :=
      bVec B V S hgen hsymm n h - bVec B V S hgen hsymm n g with hw₂
    have hw₁norm : ‖w₁‖ = ‖bVec B V S hgen hsymm n (g⁻¹ * h)‖ := by
      rw [hw₁]
      exact norm_adFlat (B.map n (iota g)).2 _
    have hclose : ‖w₂ - w₁‖ ≤ ε / (2 * Ctot) := by
      have heq : w₂ - w₁ =
          bVec B V S hgen hsymm n h -
            (adFlat (B.map n (iota g) :
                Matrix (B.model n) (B.model n) ℂ)
              (bVec B V S hgen hsymm n (g⁻¹ * h)) +
              bVec B V S hgen hsymm n g) := by
        rw [hw₂, hw₁]
        abel
      rw [heq]
      exact hdef
    have habs : |‖w₂‖ - ‖w₁‖| ≤ ε / (2 * Ctot) :=
      (abs_norm_sub_norm_le w₂ w₁).trans hclose
    have hsum : ‖w₂‖ + ‖w₁‖ ≤ Ctot := by
      rw [hCtot]
      have h2 : ‖w₂‖ ≤ sh + sg := by
        rw [hw₂]
        calc
          ‖bVec B V S hgen hsymm n h -
              bVec B V S hgen hsymm n g‖ ≤
              ‖bVec B V S hgen hsymm n h‖ +
                ‖bVec B V S hgen hsymm n g‖ := norm_sub_le _ _
          _ ≤ sh + sg := add_le_add (hnormh n) (hnormg n)
      have h1 : ‖w₁‖ ≤ sμ := by
        rw [hw₁norm]
        exact hnormμ n
      linarith
    have hdiff : |‖bVec B V S hgen hsymm n (g⁻¹ * h)‖ ^ 2 -
        ‖bVec B V S hgen hsymm n h -
          bVec B V S hgen hsymm n g‖ ^ 2| ≤ ε := by
      have hfact : ‖bVec B V S hgen hsymm n (g⁻¹ * h)‖ ^ 2 -
          ‖bVec B V S hgen hsymm n h -
            bVec B V S hgen hsymm n g‖ ^ 2 =
          (‖w₁‖ - ‖w₂‖) * (‖w₁‖ + ‖w₂‖) := by
        rw [← hw₁norm, hw₂]
        ring
      rw [hfact, abs_mul]
      have habs' : |‖w₁‖ - ‖w₂‖| ≤ ε / (2 * Ctot) := by
        rw [abs_sub_comm]
        exact habs
      have hplus : |‖w₁‖ + ‖w₂‖| ≤ Ctot := by
        rw [abs_of_nonneg (by positivity)]
        linarith [hsum]
      calc
        |‖w₁‖ - ‖w₂‖| * |‖w₁‖ + ‖w₂‖| ≤ (ε / (2 * Ctot)) * Ctot := by
          have hnn : (0 : ℝ) ≤ |‖w₁‖ - ‖w₂‖| := abs_nonneg _
          exact mul_le_mul habs' hplus (abs_nonneg _) (by positivity)
        _ ≤ ε := by
          have hne : Ctot ≠ 0 := ne_of_gt hCtotpos
          have heq : (ε / (2 * Ctot)) * Ctot = ε / 2 := by
            field_simp
          rw [heq]
          linarith
    exact hdiff

end InvolutionCollapseCocycle
end GroupApproximation
