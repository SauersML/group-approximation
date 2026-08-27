import GroupApproximation.Sofic.FinitePacketDelormeCenter
import GroupApproximation.Sofic.CollapseTransportDiagonalization

/-!
# Cofinal Delorme primitives for a general finite packet

The finite-packet circumcenter theorem produces a bounded approximate
coboundary at each fixed tolerance in the hyperfilter seminorm.  This file
selects a cofinal coordinate for each tolerance.  The resulting primitive is
bounded at every selected coordinate and its coboundary defect has the
explicit rate `2 / (j + 1)`, which is the `atTop` input needed by scaled
Kazhdan transport.

Unlike the older involution-specific diagonalization, this argument uses only
the abstract finite-packet cocycle interface.
-/

namespace GroupApproximation
namespace FinitePacketDelormeDiagonalization

open Matrix Ultralimit KazhdanCornerMatrices
open InvolutionCollapseCocycle InvolutionCollapseEndpointPrep
open CollapseTransportDiagonalization FinitePacketDelormeCenter
open scoped Matrix.Norms.L2Operator

attribute [local instance] InnerProductSpace.complexToReal

noncomputable section

variable {Γ : Type*} [Group Γ]
variable {Y : ℕ → Type*} [∀ n, Fintype (Y n)] [∀ n, DecidableEq (Y n)]

omit [Group Γ] in
/-- The coboundary defect of a bounded primitive against a bounded packet
cocycle is bounded. -/
theorem boundedSeq_defect
    (U : ∀ n, Γ → Matrix (Y n) (Y n) ℂ)
    (hU : ∀ n a, U n a ∈ Matrix.unitaryGroup (Y n) ℂ)
    (O : Γ → ∀ n, EuclideanSpace ℂ (Y n × Y n))
    (hOb : ∀ γ, IsBoundedSeq (O γ))
    {w : ∀ n, EuclideanSpace ℂ (Y n × Y n)}
    (hwb : IsBoundedSeq w) (a : Γ) :
    IsBoundedSeq (fun n ↦
      O a n - (w n - adFlat (U n a) (w n))) := by
  obtain ⟨CO, hCO⟩ := hOb a
  obtain ⟨Cw, hCw⟩ := hwb
  refine ⟨CO + (Cw + Cw), fun n ↦ ?_⟩
  calc
    ‖O a n - (w n - adFlat (U n a) (w n))‖ ≤
        ‖O a n‖ + ‖w n - adFlat (U n a) (w n)‖ := norm_sub_le _ _
    _ ≤ CO + (Cw + Cw) := by
      refine add_le_add (hCO n) ?_
      calc
        ‖w n - adFlat (U n a) (w n)‖ ≤
            ‖w n‖ + ‖adFlat (U n a) (w n)‖ := norm_sub_le _ _
        _ = ‖w n‖ + ‖w n‖ := by rw [norm_adFlat (hU n a)]
        _ ≤ Cw + Cw := add_le_add (hCw n) (hCw n)

/-- **General finite-packet Step 5 to Step 6 interface.**

From the abstract bounded almost-cocycle hypotheses, choose a cofinal
reindexing and a uniformly bounded primitive whose coboundary defect is at
most `2/(j+1)` at every selected coordinate and every mover in `T`. -/
theorem exists_cofinal_vanishing_coboundary_primitive
    (U : ∀ n, Γ → Matrix (Y n) (Y n) ℂ)
    (hU : ∀ n a, U n a ∈ Matrix.unitaryGroup (Y n) ℂ)
    (O : Γ → ∀ n, EuclideanSpace ℂ (Y n × Y n))
    (hOb : ∀ γ, IsBoundedSeq (O γ))
    (hone : ∀ n, O 1 n = 0)
    (hdefect : ∀ a γ, seqNorm (fun n ↦
      O γ n - (adFlat (U n a) (O (a⁻¹ * γ) n) + O a n)) = 0)
    {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ γ, seqNormSq (O γ) ≤ R)
    (T : Finset Γ) :
    ∃ (φ : ℕ → ℕ)
      (W : ∀ j, EuclideanSpace ℂ (Y (φ j) × Y (φ j))),
      (∀ j, j ≤ φ j) ∧ (∀ j, ‖W j‖ ≤ Real.sqrt R + 2) ∧
      ∀ a ∈ T, ∀ j,
        ‖O a (φ j) -
          (W j - adFlat (U (φ j) a) (W j))‖ ^ 2 ≤
            2 * (1 / ((j : ℝ) + 1)) := by
  classical
  have hfam : ∀ j : ℕ,
      ∃ w : ∀ n, EuclideanSpace ℂ (Y n × Y n),
        IsBoundedSeq w ∧ seqNorm w ≤ Real.sqrt R + 1 ∧
        ∀ a ∈ T, seqNormSq (fun n ↦
          O a n - (w n - adFlat (U n a) (w n))) ≤
            1 / ((j : ℝ) + 1) := by
    intro j
    exact exists_approximate_coboundary U hU O hOb hone hdefect hR0 hR T
      (by positivity)
  choose w hwb hwn hwdef using hfam
  have hgood : ∀ j : ℕ, ∀ᶠ n in ↑(Filter.hyperfilter ℕ),
      (∀ a ∈ T,
        ‖O a n - (w j n - adFlat (U n a) (w j n))‖ ^ 2 ≤
          2 * (1 / ((j : ℝ) + 1))) ∧
      ‖w j n‖ ≤ Real.sqrt R + 2 := by
    intro j
    have hdpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hfirst : ∀ᶠ n in ↑(Filter.hyperfilter ℕ), ∀ a ∈ T,
        ‖O a n - (w j n - adFlat (U n a) (w j n))‖ ^ 2 ≤
          2 * (1 / ((j : ℝ) + 1)) := by
      rw [Filter.eventually_all_finset]
      intro a ha
      have hb := boundedSeq_defect U hU O hOb (hwb j) a
      filter_upwards [eventually_norm_le_of_seqNormSq_le hb
        (hwdef j a ha) hdpos] with n hn
      have hnn := norm_nonneg
        (O a n - (w j n - adFlat (U n a) (w j n)))
      have hsqrt : Real.sqrt (2 * (1 / ((j : ℝ) + 1))) ^ 2 =
          2 * (1 / ((j : ℝ) + 1)) := Real.sq_sqrt (by positivity)
      nlinarith [hn, hnn, hsqrt,
        Real.sqrt_nonneg (2 * (1 / ((j : ℝ) + 1)))]
    have hsecond : ∀ᶠ n in ↑(Filter.hyperfilter ℕ),
        ‖w j n‖ ≤ Real.sqrt R + 2 := by
      have hlt : seqNorm (w j) < Real.sqrt R + 2 := by
        linarith [hwn j]
      filter_upwards [eventually_norm_lt_of_seqNorm_lt (hwb j) hlt] with n hn
      exact hn.le
    filter_upwards [hfirst, hsecond] with n h1 h2
    exact ⟨h1, h2⟩
  have hchoose : ∀ j : ℕ, ∃ n, j ≤ n ∧
      (∀ a ∈ T,
        ‖O a n - (w j n - adFlat (U n a) (w j n))‖ ^ 2 ≤
          2 * (1 / ((j : ℝ) + 1))) ∧
      ‖w j n‖ ≤ Real.sqrt R + 2 :=
    fun j ↦ exists_ge_of_hyperfilter_eventually (hgood j) j
  choose φ hφ hφgood using hchoose
  refine ⟨φ, fun j ↦ w j (φ j), hφ, fun j ↦ (hφgood j).2, ?_⟩
  intro a ha j
  exact (hφgood j).1 a ha

/-! ## Rank rescaling against an independently chosen mover

The diagonal primitive is constructed using exact packet movers.  The
ambient almost representation need not use those same coordinate lifts.
The following form of the rank-rescaling estimate therefore accepts an
arbitrary unitary mover.  It is the exact-mover analogue of
`CollapseTransportDiagonalization.scaledMassVanishing_rankScaled`.
-/

variable {E : Type*} [Group E]

/-- If a normalized displacement eventually vanishes and a primitive has
vanishing coboundary defect against an arbitrary unitary mover, then the
rank-rescaled primitive has scaled-mass-null displacement against that
mover. -/
theorem scaledMassVanishing_rankScaled_unitary
    (B : OpAlmostRepresentation E)
    (rho : ℕ → ℝ) (hrho : ∀ j, 0 ≤ rho j)
    (A : ∀ j, Matrix.unitaryGroup (B.model j) ℂ)
    (W b : ∀ j, EuclideanSpace ℂ (B.model j × B.model j))
    (hb : ∃ N, ∀ j ≥ N, b j = 0)
    (hdef : ∀ j,
      ‖b j - (W j - adFlat (A j :
        Matrix (B.model j) (B.model j) ℂ) (W j))‖ ^ 2 ≤
        2 * (1 / ((j : ℝ) + 1))) :
    ScaledKazhdanTransport.ScaledMassVanishing B rho (fun j ↦
      ((Real.sqrt (rho j) : ℝ) : ℂ) • unflatE (W j) -
        (A j : Matrix (B.model j) (B.model j) ℂ) *
          (((Real.sqrt (rho j) : ℝ) : ℂ) • unflatE (W j)) *
          (A j : Matrix (B.model j) (B.model j) ℂ)ᴴ) := by
  obtain ⟨N, hN⟩ := hb
  intro epsilon hepsilon
  obtain ⟨J, hJ⟩ := exists_level_two_div_le hepsilon
  refine ⟨max N J, fun j hj ↦ ?_⟩
  have hjN : N ≤ j := le_trans (le_max_left _ _) hj
  have hjJ : J ≤ j := le_trans (le_max_right _ _) hj
  have hnormeq :
      ‖W j - adFlat (A j : Matrix (B.model j) (B.model j) ℂ) (W j)‖ =
        ‖b j - (W j - adFlat (A j :
          Matrix (B.model j) (B.model j) ℂ) (W j))‖ := by
    rw [hN j hjN, zero_sub, norm_neg]
  have hsmall :
      ‖W j - adFlat (A j : Matrix (B.model j) (B.model j) ℂ) (W j)‖ ^ 2
        ≤ epsilon := by
    rw [hnormeq]
    exact (hdef j).trans (hJ j hjJ)
  rw [matMass_smul_unflatE_displacement, Real.sq_sqrt (hrho j)]
  calc
    rho j * ‖W j - adFlat (A j :
        Matrix (B.model j) (B.model j) ℂ) (W j)‖ ^ 2 ≤
        rho j * epsilon := mul_le_mul_of_nonneg_left hsmall (hrho j)
    _ = epsilon * rho j := mul_comm _ _

end

end FinitePacketDelormeDiagonalization
end GroupApproximation
