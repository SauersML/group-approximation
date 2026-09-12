import GroupApproximation.Manuscript.OneSidedMFRadical.TransportProjectionCommutation
import GroupApproximation.Manuscript.OneSidedMFRadical.TransportPrintedCommutant

/-!
# The printed characterization of `𝒞₂(V, L)` by the Kazhdan projection

`non_mf_groups_exist.tex`, the rewritten proof of Theorem `thm:transport`:

> A Hilbert--Schmidt bounded sequence `(x_n)` lies in `𝒞₂(V,L)` if and only if
> `‖P_nx_n − x_n‖₂ → 0`.
>
> In one direction, fix `ε > 0` and … `Σ a_ℓ σ̃(ℓ)` is within `ε` of `P`, so
> `limsup_n ‖P_n − Σ a_ℓ Ad(V_n(ℓ))‖ ≤ ε`.  If `(x_n) ∈ 𝒞₂(V,L)` and
> `sup_n ‖x_n‖₂ ≤ c`, then `Ad(V_n(ℓ))x_n = x_n + o(1)` in `‖·‖₂` for each
> `ℓ ∈ F`, so `limsup_n ‖P_nx_n − x_n‖₂ ≤ εc + |Σ a_ℓ − 1| c ≤ 2εc`, and `ε`
> was arbitrary.  In the other direction, `u_ℓ e_L = e_L` in `C*_max(L)`, so
> `σ̃(ℓ)P = P` and `‖Ad(V_n(ℓ))P_n − P_n‖ → 0`; if `‖P_nx_n − x_n‖₂ → 0`, then
> `‖Ad(V_n(ℓ))x_n − x_n‖₂ ≤ 2‖x_n − P_nx_n‖₂ + ‖Ad(V_n(ℓ))P_n − P_n‖ ‖x_n‖₂
> → 0`.

Both directions are proved here, one lemma each.  The splitting behind the
first is

`P_nx_n − x_n = (P_n − Σ a_ℓ Ad(V_n(ℓ)))x_n + Σ a_ℓ (Ad(V_n(ℓ))x_n − x_n)
                + (Σ a_ℓ − 1)x_n`,

and behind the second

`Ad(V_n(ℓ))x_n − x_n = Ad(V_n(ℓ))(x_n − P_nx_n) + (Ad(V_n(ℓ))P_n − P_n)x_n
                       + (P_nx_n − x_n)`.

The printed constants come out because
`Manuscript/OneSidedMFRadical/HilbertSchmidtOperatorAction.lean` supplies the
triangle inequality for `‖·‖₂` with no constant.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TransportProjectionCharacterization

open Filter Matrix Topology
open MaximalCStarKazhdanProjection
open HilbertSchmidtAdMatrix HilbertSchmidtOperatorAction TransportSigmaTilde
open TransportKazhdanProjection TransportProjectionCommutation
open TransportPrintedCommutant
open KazhdanAsymptoticCommutant
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The action of an operator is linear in the matrix it acts on. -/
theorem applyOp_sub_right (Y : FiniteModel) (M : Matrix (Y × Y) (Y × Y) ℂ)
    (a b : Matrix Y Y ℂ) :
    applyOp Y M (a - b) = applyOp Y M a - applyOp Y M b := by
  ext i j
  have hv : vecFun Y (a - b) = vecFun Y a - vecFun Y b := rfl
  rw [applyOp_apply, hv, Matrix.mulVec_sub, Pi.sub_apply, Matrix.sub_apply,
    applyOp_apply, applyOp_apply]

variable {G : Type} [Group G] (B : OpAlmostRepresentation G)
  [∀ n, Nonempty (B.model n)] (L : Subgroup G) (KD : KazhdanData ↥L)
  (f : MaximalGroupCStar ↥L →⋆ₐ[ℂ] sqCorona B)
  (Pseq : BoundedMatrixSequence (fun n ↦ sqModel (B.model n)))

omit [∀ n, Nonempty (B.model n)] in
/-- The printed `Ad(V_n(g))` acting on a matrix is `x ↦ V_n(g) x V_n(g)*`. -/
theorem applyOp_adMatrix_map (g : G) (n : ℕ)
    (a : Matrix (B.model n) (B.model n) ℂ) :
    applyOp (B.model n) (adMatrix (B.model n) (B.map n g)) a
      = (B.map n g : Matrix (B.model n) (B.model n) ℂ) * a *
        (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ :=
  applyOp_adMatrix (B.model n) _ a

omit [∀ n, Nonempty (B.model n)] in
/-- `‖·‖₂` is unchanged by the printed `Ad(V_n(g))`. -/
theorem hsNorm_applyOp_adMatrix (g : G) (n : ℕ)
    (a : Matrix (B.model n) (B.model n) ℂ) :
    hsNorm (B.model n)
        (applyOp (B.model n) (adMatrix (B.model n) (B.map n g)) a)
      = hsNorm (B.model n) a := by
  rw [applyOp_adMatrix_map B g n a]
  exact PrelimNotation.hsNorm_unitary_mul_mul (B.model n) (B.map n g).2
    (conjTranspose_mem_unitaryGroup (B.map n g).2) a

/-! ## The printed forward direction -/

/-- **"If `(x_n) ∈ 𝒞₂(V,L)` … then `limsup_n ‖P_nx_n − x_n‖₂ ≤ 2εc`, and `ε`
was arbitrary."** -/
theorem tendsto_hsNorm_applyOp_projection_sub
    (hf : ∀ s : ↥L, f (maximalGroupCStarGenerator ↥L s)
      = ((sigmaB B (L.subtype s) : unitary (sqCorona B)) : sqCorona B))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ sqModel (B.model n)) Pseq
      = f KD.projection)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) (hx : x ∈ printedCTwo B L) :
    Tendsto (fun n ↦ hsNorm (B.model n)
        (applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n) (x n) - x n))
      atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := hx.1
  have hC0 : (0 : ℝ) ≤ C := le_trans (hsNorm_nonneg (B.model 0) (x 0)) (hC 0)
  rw [Metric.tendsto_atTop]
  intro eps heps
  have hden : (0 : ℝ) < 2 * C + 2 := by linarith
  set delta : ℝ := eps / (2 * C + 2) with hdeltadef
  have hdpos : 0 < delta := div_pos heps hden
  have hde : delta * (2 * C + 2) = eps := by
    rw [hdeltadef]
    field_simp
  obtain ⟨F, alpha, hclose, hchar⟩ := exists_combination_close KD hdpos
  have hlim := limsup_norm_sub_combSeq_lt B.model B.map
    (fun g h ↦ tendsto_mul_defect B g h) L KD f Pseq hf hPmk F alpha hclose
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.cofinite
      (fun n ↦ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n
          - ∑ s ∈ F, alpha s •
            adMatrix (B.model n) (B.map n (L.subtype s))‖) := by
    refine Filter.isBoundedUnder_of ⟨‖Pseq‖ + ∑ s ∈ F, ‖alpha s‖, fun n ↦ ?_⟩
    refine (norm_sub_le _ _).trans (add_le_add
      (boundedMatrixSequence_coord_norm_le (fun n ↦ sqModel (B.model n))
        Pseq n) ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ ↦ ?_)
    rw [norm_smul]
    have h1 : ‖adMatrix (B.model n) (B.map n (L.subtype s))‖ = 1 :=
      CStarRing.norm_of_mem_unitary
        (adMatrix_mem_unitary (B.model n) (B.map n (L.subtype s)).2)
    rw [h1, mul_one]
  have hev1 : ∀ᶠ n in atTop, ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
        (sqModel (B.model n)) ℂ) n
      - ∑ s ∈ F, alpha s • adMatrix (B.model n) (B.map n (L.subtype s))‖
      < delta := by
    have h := Filter.eventually_lt_of_limsup_lt hlim hbdd
    rwa [Nat.cofinite_eq_atTop] at h
  have hone : ∀ s : ↥L, Tendsto (fun n ↦ ‖alpha s‖ * hsNorm (B.model n)
      (applyOp (B.model n) (adMatrix (B.model n)
        (B.map n (L.subtype s))) (x n) - x n)) atTop (nhds 0) := by
    intro s
    have h := ((isHSAsymptoticallyCentral_iff_adjointSequence B L x).mp hx.2)
      (L.subtype s) s.2
    have h2 : Tendsto (fun n ↦ hsNorm (B.model n)
        (applyOp (B.model n) (adMatrix (B.model n)
          (B.map n (L.subtype s))) (x n) - x n)) atTop (nhds 0) := by
      refine h.congr fun n ↦ ?_
      rw [applyOp_adMatrix_map B (L.subtype s) n (x n)]
      rfl
    simpa using h2.const_mul ‖alpha s‖
  have hmid : Tendsto (fun n ↦ ∑ s ∈ F, ‖alpha s‖ * hsNorm (B.model n)
      (applyOp (B.model n) (adMatrix (B.model n)
        (B.map n (L.subtype s))) (x n) - x n)) atTop (nhds 0) := by
    have h := tendsto_finsetSum F fun s (_ : s ∈ F) ↦ hone s
    simpa using h
  have hev2 : ∀ᶠ n in atTop, ∑ s ∈ F, ‖alpha s‖ * hsNorm (B.model n)
      (applyOp (B.model n) (adMatrix (B.model n)
        (B.map n (L.subtype s))) (x n) - x n) < delta := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hmid) delta hdpos
    filter_upwards [eventually_ge_atTop N] with n hn
    have h2 := hN n hn
    rw [Real.dist_eq, sub_zero] at h2
    exact lt_of_abs_lt h2
  have hgoal : ∀ᶠ n in atTop, dist (hsNorm (B.model n)
      (applyOp (B.model n)
        ((Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n) (x n) - x n)) 0 < eps := by
    filter_upwards [hev1, hev2] with n h1 h2
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNorm_nonneg _ _)]
    have hcard : 0 < Fintype.card (B.model n) := B.modelNonempty n
    have e1 : applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n
            - ∑ s ∈ F, alpha s •
              adMatrix (B.model n) (B.map n (L.subtype s))) (x n)
        = applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n)
          - ∑ s ∈ F, alpha s • applyOp (B.model n)
              (adMatrix (B.model n) (B.map n (L.subtype s))) (x n) := by
      rw [applyOp_sub, applyOp_sum]
      congr 1
      exact Finset.sum_congr rfl fun s _ ↦ applyOp_smul _ _ _ _
    have e2 : (∑ s ∈ F, alpha s •
          (applyOp (B.model n) (adMatrix (B.model n)
            (B.map n (L.subtype s))) (x n) - x n))
        = (∑ s ∈ F, alpha s • applyOp (B.model n)
            (adMatrix (B.model n) (B.map n (L.subtype s))) (x n))
          - (∑ s ∈ F, alpha s) • x n := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ ↦ smul_sub _ _ _
    have hsplit : applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n) (x n) - x n
        = applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
                (sqModel (B.model n)) ℂ) n
              - ∑ s ∈ F, alpha s •
                adMatrix (B.model n) (B.map n (L.subtype s))) (x n)
          + (∑ s ∈ F, alpha s •
              (applyOp (B.model n) (adMatrix (B.model n)
                (B.map n (L.subtype s))) (x n) - x n))
          + ((∑ s ∈ F, alpha s) - 1) • x n := by
      rw [e1, e2, sub_smul, one_smul, sub_add_sub_cancel, sub_add_sub_cancel]
    have hb1 : hsNorm (B.model n) (applyOp (B.model n)
        ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n
          - ∑ s ∈ F, alpha s •
            adMatrix (B.model n) (B.map n (L.subtype s))) (x n))
        ≤ delta * C :=
      le_trans (hsNorm_applyOp_le (B.model n) hcard _ _)
        (mul_le_mul h1.le (hC n) (hsNorm_nonneg _ _) hdpos.le)
    have hb2 : hsNorm (B.model n) (∑ s ∈ F, alpha s •
          (applyOp (B.model n) (adMatrix (B.model n)
            (B.map n (L.subtype s))) (x n) - x n))
        ≤ ∑ s ∈ F, ‖alpha s‖ * hsNorm (B.model n)
            (applyOp (B.model n) (adMatrix (B.model n)
              (B.map n (L.subtype s))) (x n) - x n) := by
      refine le_trans (hsNorm_sum_le (B.model n) hcard F _) ?_
      exact Finset.sum_le_sum fun s _ ↦
        le_of_eq (hsNorm_smul (B.model n) hcard _ _)
    have hb3 : hsNorm (B.model n) (((∑ s ∈ F, alpha s) - 1) • x n)
        ≤ delta * C := by
      rw [hsNorm_smul (B.model n) hcard]
      exact mul_le_mul hchar.le (hC n) (hsNorm_nonneg _ _) hdpos.le
    have htri : hsNorm (B.model n) (applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n) (x n) - x n)
        ≤ hsNorm (B.model n) (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
                (sqModel (B.model n)) ℂ) n
              - ∑ s ∈ F, alpha s •
                adMatrix (B.model n) (B.map n (L.subtype s))) (x n))
          + hsNorm (B.model n) (∑ s ∈ F, alpha s •
              (applyOp (B.model n) (adMatrix (B.model n)
                (B.map n (L.subtype s))) (x n) - x n))
          + hsNorm (B.model n) (((∑ s ∈ F, alpha s) - 1) • x n) := by
      rw [hsplit]
      refine le_trans (hsNorm_add_le (B.model n) hcard _ _) ?_
      have := hsNorm_add_le (B.model n) hcard
        (applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n
            - ∑ s ∈ F, alpha s •
              adMatrix (B.model n) (B.map n (L.subtype s))) (x n))
        (∑ s ∈ F, alpha s •
          (applyOp (B.model n) (adMatrix (B.model n)
            (B.map n (L.subtype s))) (x n) - x n))
      linarith
    have hprod : delta * (2 * C + 2) = 2 * (delta * C) + 2 * delta := by ring
    linarith [htri, hb1, hb2, hb3, h2, hde, hdpos, hprod]
  exact eventually_atTop.mp hgoal

/-! ## The printed reverse direction -/

/-- **"`u_ℓ e_L = e_L` in `C*_max(L)`, so `σ̃(ℓ)P = P` and
`‖Ad(V_n(ℓ))P_n − P_n‖ → 0`."** -/
theorem tendsto_norm_adMatrix_mul_projection_sub
    (hf : ∀ s : ↥L, f (maximalGroupCStarGenerator ↥L s)
      = ((sigmaB B (L.subtype s) : unitary (sqCorona B)) : sqCorona B))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ sqModel (B.model n)) Pseq
      = f KD.projection)
    {ell : G} (hell : ell ∈ L) :
    Tendsto (fun n ↦ ‖adMatrix (B.model n) (B.map n ell) *
        (Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n
      - (Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n‖) atTop (nhds 0) := by
  have hfix : ((sigmaB B ell : unitary (sqCorona B)) : sqCorona B) *
      f KD.projection = f KD.projection :=
    rep_mul_image KD ((sigmaB B).comp L.subtype) f hf ⟨ell, hell⟩
  have hmulmk := map_mul (normMatrixCStarCoronaMk (fun n ↦ sqModel (B.model n)))
    (unitarySequenceBounded (fun n ↦ sqModel (B.model n))
      (adUnitary B.model B.map ell)) Pseq
  have hsubmk := map_sub (normMatrixCStarCoronaMk (fun n ↦ sqModel (B.model n)))
    (unitarySequenceBounded (fun n ↦ sqModel (B.model n))
      (adUnitary B.model B.map ell) * Pseq) Pseq
  have hzero : normMatrixCStarCoronaMk (fun n ↦ sqModel (B.model n))
      (unitarySequenceBounded (fun n ↦ sqModel (B.model n))
        (adUnitary B.model B.map ell) * Pseq - Pseq) = 0 := by
    rw [hsubmk, hmulmk, hPmk, sigmaB_coe B ell] at *
    rw [hfix, sub_self]
  have hnull := (normMatrixCStarCoronaMk_eq_zero_iff
    (fun n ↦ sqModel (B.model n)) _).mp hzero
  rw [IsNullMatrixSequence, Nat.cofinite_eq_atTop] at hnull
  refine hnull.congr fun n ↦ ?_
  refine congrArg _ ?_
  rw [lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_mul, Pi.mul_apply]
  rfl

/-- **"if `‖P_nx_n − x_n‖₂ → 0`, then `‖Ad(V_n(ℓ))x_n − x_n‖₂ → 0`."** -/
theorem isHSAsymptoticallyCentral_of_tendsto
    (hf : ∀ s : ↥L, f (maximalGroupCStarGenerator ↥L s)
      = ((sigmaB B (L.subtype s) : unitary (sqCorona B)) : sqCorona B))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ sqModel (B.model n)) Pseq
      = f KD.projection)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    {C : ℝ} (hC : ∀ n, hsNorm (B.model n) (x n) ≤ C)
    (h : Tendsto (fun n ↦ hsNorm (B.model n)
      (applyOp (B.model n)
        ((Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n) (x n) - x n)) atTop (nhds 0)) :
    IsHSAsymptoticallyCentral B L x := by
  have hC0 : (0 : ℝ) ≤ C := le_trans (hsNorm_nonneg (B.model 0) (x 0)) (hC 0)
  rw [isHSAsymptoticallyCentral_iff_adjointSequence]
  intro ell hell
  have hcomm := tendsto_norm_adMatrix_mul_projection_sub B L KD f Pseq hf hPmk
    hell
  have hbound : ∀ n, hsNorm (B.model n)
      (applyOp (B.model n) (adMatrix (B.model n) (B.map n ell)) (x n) - x n)
      ≤ 2 * hsNorm (B.model n) (applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n) (x n) - x n)
        + ‖adMatrix (B.model n) (B.map n ell) *
            (Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n
          - (Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n‖ * C := by
    intro n
    have hcard : 0 < Fintype.card (B.model n) := B.modelNonempty n
    have hsplit : applyOp (B.model n)
          (adMatrix (B.model n) (B.map n ell)) (x n) - x n
        = applyOp (B.model n) (adMatrix (B.model n) (B.map n ell))
            (x n - applyOp (B.model n)
              ((Pseq : ∀ n, Matrix (sqModel (B.model n))
                (sqModel (B.model n)) ℂ) n) (x n))
          + applyOp (B.model n) (adMatrix (B.model n) (B.map n ell) *
              (Pseq : ∀ n, Matrix (sqModel (B.model n))
                (sqModel (B.model n)) ℂ) n
              - (Pseq : ∀ n, Matrix (sqModel (B.model n))
                (sqModel (B.model n)) ℂ) n) (x n)
          + (applyOp (B.model n)
              ((Pseq : ∀ n, Matrix (sqModel (B.model n))
                (sqModel (B.model n)) ℂ) n) (x n) - x n) := by
      rw [applyOp_sub_right, applyOp_sub, applyOp_mul, sub_add_sub_cancel,
        sub_add_sub_cancel]
    have hA : hsNorm (B.model n) (applyOp (B.model n)
        (adMatrix (B.model n) (B.map n ell))
          (x n - applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n)))
        = hsNorm (B.model n) (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n) - x n) := by
      rw [hsNorm_applyOp_adMatrix B ell n]
      exact AmenableTraceHyperlinear.hsNorm_sub_comm (B.model n) _ _
    have hB : hsNorm (B.model n) (applyOp (B.model n)
        (adMatrix (B.model n) (B.map n ell) *
            (Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n
          - (Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n))
        ≤ ‖adMatrix (B.model n) (B.map n ell) *
            (Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n
          - (Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n‖ * C :=
      le_trans (hsNorm_applyOp_le (B.model n) hcard _ _)
        (mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _))
    have htri := hsNorm_add_le (B.model n) hcard
      (applyOp (B.model n) (adMatrix (B.model n) (B.map n ell))
          (x n - applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n))
        + applyOp (B.model n) (adMatrix (B.model n) (B.map n ell) *
            (Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n
            - (Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n))
      (applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n) (x n) - x n)
    have htri2 := hsNorm_add_le (B.model n) hcard
      (applyOp (B.model n) (adMatrix (B.model n) (B.map n ell))
        (x n - applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n) (x n)))
      (applyOp (B.model n) (adMatrix (B.model n) (B.map n ell) *
          (Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n
          - (Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n) (x n))
    rw [hsplit]
    linarith [htri, htri2, hA, hB]
  have hlim : Tendsto (fun n ↦ 2 * hsNorm (B.model n)
      (applyOp (B.model n)
        ((Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n) (x n) - x n)
      + ‖adMatrix (B.model n) (B.map n ell) *
          (Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n
        - (Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n‖ * C) atTop (nhds 0) := by
    have h1 := h.const_mul (2 : ℝ)
    have h2 := hcomm.mul_const C
    simpa using h1.add h2
  refine (squeeze_zero (fun n ↦ hsNorm_nonneg (B.model n) _) hbound hlim).congr
    fun n ↦ ?_
  rw [applyOp_adMatrix_map B ell n (x n)]
  rfl

end

end TransportProjectionCharacterization
end OneSidedMFRadical
end Manuscript
end GroupApproximation
