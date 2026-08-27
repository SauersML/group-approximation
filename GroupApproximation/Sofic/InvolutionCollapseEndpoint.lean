import GroupApproximation.Sofic.CollapsePrintedProfile
import GroupApproximation.Sofic.CollapseProfileBoundNumeric
import GroupApproximation.Sofic.CollapseTransportEndpoint
import GroupApproximation.Sofic.InvolutionCollapseEndpointPrep
import GroupApproximation.Sofic.TorsionCompressionCollapse
import GroupApproximation.Algebra.CountableInstances

/-!
# The unconditional involutive compression collapse

The summit of the collapse formalization.  Let `ι : Γ →* E` be a
homomorphism from a countable Kazhdan group, `s ∈ E` a one-sided
compressor (`s ι(Γ) s⁻¹ ≤ ι(Γ)`), and `k ∈ E` an involution whose
`ι(Γ)`-orbit commutes elementwise and whose conjugates by the compressed
copy `s ι(Γ) s⁻¹` centralize `k`.  Then **no marked operator-norm almost
representation of `E` can separate the collapse commutator `⁅ι(γ₀), k⁆`
from the identity** — so in every norm matrix corona representation of
`E` the commutator dies.  There are no hypotheses beyond the group
theory: property `(T)` is consumed through the in-repo Delorme theorem,
and every analytic step is quantitative.

The proof runs the full ladder at once: corrected involution microstates
(`InvolutionOrbitMicrostates`), the rank metric and its normalized
displacement vectors (`InvolutionCollapseMetric`, `…Profile`), the
bound on the limiting displacement profile *by its generator values*
(`Sofic.CollapseProfileBound`, over
`Kazhdan.UltralimitGaussianBoundedness`), one approximate coboundary
primitive from sequence-level circumcenters (`…Center`), and — for Step 6 —
the weighted Kazhdan transport at the rank weight `w_n = k_n`
(`Sofic.CollapseTransportEndpoint`, over `ScaledKazhdanTransport`), which
contradicts the nonvanishing mass anchor of a marked model.

Step 6 travels the rank-weight transport, **not** the Hilbert-space
ultraproduct argument that `thm:collapse` prints; the divergence, and why this
development cannot contain the printed route, is recorded in the docstring of
`Sofic/CollapseScaledStepSix.lean`.  The one-stage corner assembly of
`rem:collapse-finite-stage` remains in this file as
`stage_conj_displacement`, `stage_capture`, `stage_transport_bound` and
`numeric_transport_bound`, which are what the remark's three badges cite; it is
no longer the route `no_marked_model` takes.
-/

namespace GroupApproximation
namespace InvolutionCollapseEndpoint

open Matrix InvolutionOrbitMicrostates InvolutionRankMass
open InvolutionCollapseMetric InvolutionMicrostateTools
open InvolutionCollapseProfile InvolutionCollapseCocycle
open InvolutionCollapseCenter InvolutionCollapseIndexCapture
open InvolutionCollapseEndpointPrep
open Ultralimit KazhdanCornerMatrices KazhdanCompressorCorner
open scoped Matrix.Norms.L2Operator
open scoped commutatorElement

attribute [local instance] InnerProductSpace.complexToReal

/-- The flattening isometry is inverse to unflattening. -/
theorem flatE_unflatE {Y : Type*} [Fintype Y]
    (x : EuclideanSpace ℂ (Y × Y)) : flatE (unflatE x) = x := by
  ext p
  rfl

/-- Cofinitely eventual facts hold hyperfilter-eventually. -/
theorem hyperfilter_eventually_of_exists {P : ℕ → Prop}
    (h : ∃ N, ∀ n ≥ N, P n) :
    ∀ᶠ n in ↑(Filter.hyperfilter ℕ), P n := by
  obtain ⟨N, hN⟩ := h
  have hcofin : ∀ᶠ n in Filter.cofinite, P n := by
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (Set.finite_Iio N) fun n hn ↦ ?_
    rw [Set.mem_Iio]
    by_contra hge
    exact hn (hN n (le_of_not_gt hge))
  exact hcofin.filter_mono (Filter.hyperfilter_le_cofinite)


/-- Pure real arithmetic of the transport constants: with the corner
tolerance and the primitive tolerance chosen from `ρt`, the transported
mass bound is at most `(ρt / 2)²`. -/
theorem numeric_transport_bound :
    ∀ {Cw ρt θ τ q : ℝ}
      (_hCwpos : 0 < Cw) (_hgap : 0 < 1 - θ)
      (_hqdef : q = ρt / (24 * (Cw + 1)))
      (_hτr : τ ≤ (1 - θ) * ρt ^ 2 / (256 * (Cw + 1))),
      18 * q ^ 2 * Cw ^ 2 + 16 * ((Cw + 1) * (2 * τ) / (1 - θ)) ≤
        (ρt / 2) ^ 2 := by
  intro Cw ρt θ τ q hCwpos hgap hqdef hτr
  have hq2 : q ^ 2 = ρt ^ 2 / (576 * (Cw + 1) ^ 2) := by
    rw [hqdef, div_pow]
    congr 1
    ring
  have hA : 18 * q ^ 2 * Cw ^ 2 ≤ ρt ^ 2 / 8 := by
    have hrw : 18 * q ^ 2 * Cw ^ 2 =
        18 * ρt ^ 2 * Cw ^ 2 / (576 * (Cw + 1) ^ 2) := by
      rw [hq2]
      ring
    rw [hrw, div_le_div_iff₀ (by nlinarith [hCwpos] :
      (0 : ℝ) < 576 * (Cw + 1) ^ 2) (by norm_num : (0 : ℝ) < 8)]
    have hkey : 144 * Cw ^ 2 ≤ 576 * (Cw + 1) ^ 2 := by
      nlinarith [hCwpos]
    nlinarith [mul_le_mul_of_nonneg_left hkey (sq_nonneg ρt)]
  have hBnum : 16 * ((Cw + 1) * (2 * τ) / (1 - θ)) ≤ ρt ^ 2 / 8 := by
    have hrw : 16 * ((Cw + 1) * (2 * τ) / (1 - θ)) =
        32 * (Cw + 1) * τ / (1 - θ) := by ring
    rw [hrw, div_le_div_iff₀ hgap (by norm_num : (0 : ℝ) < 8)]
    have h256 : (0 : ℝ) < 256 * (Cw + 1) := by nlinarith [hCwpos]
    have h2 := mul_le_mul_of_nonneg_left hτr (le_of_lt h256)
    have h3' : 256 * (Cw + 1) * ((1 - θ) * ρt ^ 2 / (256 * (Cw + 1))) =
        (1 - θ) * ρt ^ 2 := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ (ne_of_gt h256)
    nlinarith [h2, h3']
  have hq4 : (ρt / 2) ^ 2 = ρt ^ 2 / 4 := by ring
  rw [hq4]
  linarith [hA, hBnum]

/-- **Per-generator displacement of the compressed primitive.**  The
compression of the primitive matrix by a unitary is moved by at most
`2τ` in Frobenius norm by each generator, given the primitive's own
displacement bound and the mixed conjugation defect. -/
theorem stage_conj_displacement {Y : Type*} [Fintype Y] [DecidableEq Y]
    {Us Ua Ud W : Matrix Y Y ℂ} {wv : EuclideanSpace ℂ (Y × Y)}
    (hUsmem : Us ∈ Matrix.unitaryGroup Y ℂ)
    (hUamem : Ua ∈ Matrix.unitaryGroup Y ℂ)
    (hUdmem : Ud ∈ Matrix.unitaryGroup Y ℂ)
    (hW : W = unflatE wv) {Cw τ ε₆ : ℝ}
    (hCwpos : 0 < Cw) (_hτpos : 0 < τ) (hε6pos : 0 < ε₆)
    (h3 : ‖wv‖ ≤ Cw)
    (h2 : ‖wv - adFlat Ud wv‖ ≤ τ)
    (hA12' : ‖Ua * Usᴴ - Usᴴ * Ud‖ ≤ ε₆)
    (hε6Cw : ε₆ * Cw ≤ τ / 2) :
    Real.sqrt (ScaledKazhdanTransport.matMass
      (Usᴴ * W * Us - Ua * (Usᴴ * W * Us) * Uaᴴ)) ≤ 2 * τ := by
  have hmassWval : ScaledKazhdanTransport.matMass W = ‖wv‖ ^ 2 := by
    rw [← norm_flatE_sq, hW, flatE_unflatE]
  have hbridged : ‖wv - adFlat Ud wv‖ ^ 2 =
      ScaledKazhdanTransport.matMass (W - Ud * W * Udᴴ) := by
    have hflat : wv - adFlat Ud wv = flatE (W - Ud * W * Udᴴ) := by
      rw [flatE_sub, hW, flatE_unflatE]
      rfl
    rw [hflat, norm_flatE_sq]
  have hsplit : Usᴴ * W * Us - Ua * (Usᴴ * W * Us) * Uaᴴ =
      Usᴴ * (W - Ud * W * Udᴴ) * Us +
        ((Usᴴ * Ud) * W * (Usᴴ * Ud)ᴴ -
          (Ua * Usᴴ) * W * (Ua * Usᴴ)ᴴ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    noncomm_ring
  have hflatnorm : ∀ Z : Matrix Y Y ℂ,
      ‖flatE Z‖ = Real.sqrt (ScaledKazhdanTransport.matMass Z) := by
    intro Z
    rw [← Real.sqrt_sq (norm_nonneg (flatE Z)), norm_flatE_sq]
  have hterm1 : Real.sqrt (ScaledKazhdanTransport.matMass
      (Usᴴ * (W - Ud * W * Udᴴ) * Us)) ≤ τ := by
    have hconj := ScaledKazhdanTransport.matMass_unitary_conj
      (conjTranspose_mem_unitaryGroup hUsmem) (W - Ud * W * Udᴴ)
    rw [Matrix.conjTranspose_conjTranspose] at hconj
    rw [hconj, ← hbridged, Real.sqrt_sq (norm_nonneg _)]
    exact h2
  have hA12 : ‖(Usᴴ * Ud) - (Ua * Usᴴ)‖ ≤ ε₆ := by
    rw [norm_sub_rev]
    exact hA12'
  have hterm2 : Real.sqrt (ScaledKazhdanTransport.matMass
      ((Usᴴ * Ud) * W * (Usᴴ * Ud)ᴴ -
        (Ua * Usᴴ) * W * (Ua * Usᴴ)ᴴ)) ≤ 2 * (ε₆ * Cw) := by
    set A₁ : Matrix Y Y ℂ := Usᴴ * Ud with hA₁
    set A₂ : Matrix Y Y ℂ := Ua * Usᴴ with hA₂
    have hsplit2 : A₁ * W * A₁ᴴ - A₂ * W * A₂ᴴ =
        (A₁ - A₂) * W * A₁ᴴ + A₂ * W * (A₁ - A₂)ᴴ := by
      simp only [Matrix.conjTranspose_sub]
      noncomm_ring
    have hA1norm : ‖A₁ᴴ‖ ≤ 1 := by
      rw [← Matrix.star_eq_conjTranspose, norm_star]
      exact norm_le_one_of_mem_unitary
        (Submonoid.mul_mem _ (conjTranspose_mem_unitaryGroup hUsmem)
          hUdmem)
    have hA2norm : ‖A₂‖ ≤ 1 :=
      norm_le_one_of_mem_unitary
        (Submonoid.mul_mem _ hUamem
          (conjTranspose_mem_unitaryGroup hUsmem))
    have hmw : ScaledKazhdanTransport.matMass W ≤ Cw ^ 2 := by
      rw [hmassWval]
      nlinarith [h3, norm_nonneg wv]
    have hmass1 : ScaledKazhdanTransport.matMass
        ((A₁ - A₂) * W * A₁ᴴ) ≤ ε₆ ^ 2 * (Cw ^ 2) := by
      calc
        ScaledKazhdanTransport.matMass ((A₁ - A₂) * W * A₁ᴴ) ≤
            ‖A₁ᴴ‖ ^ 2 * ScaledKazhdanTransport.matMass
              ((A₁ - A₂) * W) :=
          ScaledKazhdanTransport.matMass_mul_le_right _ _
        _ ≤ ‖A₁ᴴ‖ ^ 2 * (‖A₁ - A₂‖ ^ 2 *
            ScaledKazhdanTransport.matMass W) :=
          mul_le_mul_of_nonneg_left
            (ScaledKazhdanTransport.matMass_mul_le_left _ _)
            (sq_nonneg _)
        _ ≤ ε₆ ^ 2 * (Cw ^ 2) := by
          have h1' : ‖A₁ - A₂‖ ^ 2 ≤ ε₆ ^ 2 := by
            nlinarith [norm_nonneg (A₁ - A₂), hA12]
          have h2' : ‖A₁ᴴ‖ ^ 2 ≤ 1 := by
            nlinarith [norm_nonneg A₁ᴴ, hA1norm]
          have hinner : ‖A₁ - A₂‖ ^ 2 *
              ScaledKazhdanTransport.matMass W ≤ ε₆ ^ 2 * Cw ^ 2 :=
            mul_le_mul h1' hmw
              (ScaledKazhdanTransport.matMass_nonneg W) (sq_nonneg ε₆)
          calc
            ‖A₁ᴴ‖ ^ 2 * (‖A₁ - A₂‖ ^ 2 *
                ScaledKazhdanTransport.matMass W) ≤
                1 * (ε₆ ^ 2 * Cw ^ 2) :=
              mul_le_mul h2' hinner
                (mul_nonneg (sq_nonneg _)
                  (ScaledKazhdanTransport.matMass_nonneg W))
                one_pos.le
            _ = ε₆ ^ 2 * (Cw ^ 2) := by ring
    have hmass2 : ScaledKazhdanTransport.matMass
        (A₂ * W * (A₁ - A₂)ᴴ) ≤ ε₆ ^ 2 * (Cw ^ 2) := by
      calc
        ScaledKazhdanTransport.matMass (A₂ * W * (A₁ - A₂)ᴴ) ≤
            ‖(A₁ - A₂)ᴴ‖ ^ 2 * ScaledKazhdanTransport.matMass
              (A₂ * W) :=
          ScaledKazhdanTransport.matMass_mul_le_right _ _
        _ ≤ ‖(A₁ - A₂)ᴴ‖ ^ 2 * (‖A₂‖ ^ 2 *
            ScaledKazhdanTransport.matMass W) :=
          mul_le_mul_of_nonneg_left
            (ScaledKazhdanTransport.matMass_mul_le_left _ _)
            (sq_nonneg _)
        _ ≤ ε₆ ^ 2 * (Cw ^ 2) := by
          have hstar : ‖(A₁ - A₂)ᴴ‖ = ‖A₁ - A₂‖ := by
            rw [← Matrix.star_eq_conjTranspose, norm_star]
          have h1' : ‖A₁ - A₂‖ ^ 2 ≤ ε₆ ^ 2 := by
            nlinarith [norm_nonneg (A₁ - A₂), hA12]
          have h2' : ‖A₂‖ ^ 2 ≤ 1 := by
            nlinarith [norm_nonneg A₂, hA2norm]
          have hinner : ‖A₂‖ ^ 2 *
              ScaledKazhdanTransport.matMass W ≤ 1 * Cw ^ 2 :=
            mul_le_mul h2' hmw
              (ScaledKazhdanTransport.matMass_nonneg W) one_pos.le
          rw [hstar]
          calc
            ‖A₁ - A₂‖ ^ 2 * (‖A₂‖ ^ 2 *
                ScaledKazhdanTransport.matMass W) ≤
                ε₆ ^ 2 * (1 * Cw ^ 2) :=
              mul_le_mul h1' hinner
                (mul_nonneg (sq_nonneg _)
                  (ScaledKazhdanTransport.matMass_nonneg W))
                (sq_nonneg ε₆)
            _ = ε₆ ^ 2 * (Cw ^ 2) := by ring
    have hsqrt1 : Real.sqrt (ScaledKazhdanTransport.matMass
        ((A₁ - A₂) * W * A₁ᴴ)) ≤ ε₆ * Cw := by
      have h := Real.sqrt_le_sqrt hmass1
      rwa [show ε₆ ^ 2 * Cw ^ 2 = (ε₆ * Cw) ^ 2 by ring,
        Real.sqrt_sq (mul_nonneg hε6pos.le hCwpos.le)] at h
    have hsqrt2 : Real.sqrt (ScaledKazhdanTransport.matMass
        (A₂ * W * (A₁ - A₂)ᴴ)) ≤ ε₆ * Cw := by
      have h := Real.sqrt_le_sqrt hmass2
      rwa [show ε₆ ^ 2 * Cw ^ 2 = (ε₆ * Cw) ^ 2 by ring,
        Real.sqrt_sq (mul_nonneg hε6pos.le hCwpos.le)] at h
    calc
      Real.sqrt (ScaledKazhdanTransport.matMass
          (A₁ * W * A₁ᴴ - A₂ * W * A₂ᴴ)) =
          ‖flatE (A₁ * W * A₁ᴴ - A₂ * W * A₂ᴴ)‖ :=
        (hflatnorm _).symm
      _ = ‖flatE ((A₁ - A₂) * W * A₁ᴴ) +
          flatE (A₂ * W * (A₁ - A₂)ᴴ)‖ := by
        rw [← flatE_add, hsplit2]
      _ ≤ ‖flatE ((A₁ - A₂) * W * A₁ᴴ)‖ +
          ‖flatE (A₂ * W * (A₁ - A₂)ᴴ)‖ := norm_add_le _ _
      _ ≤ 2 * (ε₆ * Cw) := by
        rw [hflatnorm, hflatnorm]
        linarith [hsqrt1, hsqrt2]
  calc
    Real.sqrt (ScaledKazhdanTransport.matMass
        (Usᴴ * W * Us - Ua * (Usᴴ * W * Us) * Uaᴴ)) =
        ‖flatE (Usᴴ * W * Us - Ua * (Usᴴ * W * Us) * Uaᴴ)‖ :=
      (hflatnorm _).symm
    _ = ‖flatE (Usᴴ * (W - Ud * W * Udᴴ) * Us) +
        flatE ((Usᴴ * Ud) * W * (Usᴴ * Ud)ᴴ -
          (Ua * Usᴴ) * W * (Ua * Usᴴ)ᴴ)‖ := by
      rw [← flatE_add, hsplit]
    _ ≤ ‖flatE (Usᴴ * (W - Ud * W * Udᴴ) * Us)‖ +
        ‖flatE ((Usᴴ * Ud) * W * (Usᴴ * Ud)ᴴ -
          (Ua * Usᴴ) * W * (Ua * Usᴴ)ᴴ)‖ := norm_add_le _ _
    _ ≤ 2 * τ := by
      rw [hflatnorm, hflatnorm]
      have := hterm1
      have := hterm2
      linarith [hε6Cw]


/-- Boundedness of the coboundary difference of a bounded sequence. -/
theorem ydiff_bounded {Γ E : Type} [Group Γ] [Group E]
    (B : OpAlmostRepresentation E) (iota : Γ →* E)
    {w : ∀ n, EuclideanSpace ℂ (B.model n × B.model n)}
    (hwbdd : IsBoundedSeq w) (a : Γ) :
    IsBoundedSeq (fun n ↦
      w n - adFlat (B.map n (iota a) :
        Matrix (B.model n) (B.model n) ℂ) (w n)) := by
  obtain ⟨Cb, hCb⟩ := id hwbdd
  refine ⟨Cb + Cb, fun n ↦ ?_⟩
  have h3 : ‖adFlat (B.map n (iota a) :
      Matrix (B.model n) (B.model n) ℂ) (w n)‖ = ‖w n‖ := by
    rw [norm_adFlat (B.map n (iota a)).2]
  calc
    ‖w n - adFlat (B.map n (iota a) :
        Matrix (B.model n) (B.model n) ℂ) (w n)‖ ≤
        ‖w n‖ + ‖adFlat (B.map n (iota a) :
          Matrix (B.model n) (B.model n) ℂ) (w n)‖ := norm_sub_le _ _
    _ ≤ Cb + Cb := by
      rw [h3]
      exact add_le_add (hCb n) (hCb n)

/-- Boundedness of the displacement-minus-coboundary sequence. -/
theorem xdiff_bounded {Γ E : Type} [Group Γ] [Group E]
    (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ) (S : Finset Γ)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    {w : ∀ n, EuclideanSpace ℂ (B.model n × B.model n)}
    (hwbdd : IsBoundedSeq w) (a : Γ) :
    IsBoundedSeq (fun n ↦
      bVec B V S hgen hsymm n a -
        (w n - adFlat (B.map n (iota a) :
          Matrix (B.model n) (B.model n) ℂ) (w n))) := by
  obtain ⟨Ca, hCa⟩ :=
    id (isBoundedSeq_bVec B V S hgen hsymm hVinv hVcomm a)
  obtain ⟨Cy, hCy⟩ := id (ydiff_bounded B iota hwbdd a)
  refine ⟨Ca + Cy, fun n ↦ ?_⟩
  calc
    ‖bVec B V S hgen hsymm n a -
        (w n - adFlat (B.map n (iota a) :
          Matrix (B.model n) (B.model n) ℂ) (w n))‖ ≤
        ‖bVec B V S hgen hsymm n a‖ +
          ‖w n - adFlat (B.map n (iota a) :
            Matrix (B.model n) (B.model n) ℂ) (w n)‖ := norm_sub_le _ _
    _ ≤ Ca + Cy := add_le_add (hCa n) (hCy n)

/-- Boundedness of the displacement-minus-coboundary sequence, for the
**printed** displacement vector of Step 4. -/
theorem xdiff_bounded_printed {Γ E : Type} [Group Γ] [Group E]
    (B : OpAlmostRepresentation E) (iota : Γ →* E) (k : E)
    (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ) (S : Finset Γ)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    {w : ∀ n, EuclideanSpace ℂ (B.model n × B.model n)}
    (hwbdd : IsBoundedSeq w) (a : Γ) :
    IsBoundedSeq (fun n ↦
      CollapseWordMetric.bVec B V S n a -
        (w n - adFlat (B.map n (iota a) :
          Matrix (B.model n) (B.model n) ℂ) (w n))) :=
  (CollapsePrintedProfile.isBoundedSeq_printed B iota k V S hgen hsymm hVinv
    hVcomm hVconv a).sub (ydiff_bounded B iota hwbdd a)

/-- **The coboundary defect is the same for the two displacement vectors.**
The guarded vector of `InvolutionCollapseProfile` and the printed vector of
Step 4 agree at all large stages, so their coboundary defects against a fixed
primitive have the same limiting squared seminorm.  This is what lets the
circumcenter of Step 5 be run once and read off for the printed object. -/
theorem seqNormSq_xdiff_printed_eq {Γ E : Type} [Group Γ] [Group E]
    (B : OpAlmostRepresentation E) (iota : Γ →* E) (k : E)
    (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ) (S : Finset Γ)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    {w : ∀ n, EuclideanSpace ℂ (B.model n × B.model n)}
    (hwbdd : IsBoundedSeq w) (a : Γ) :
    seqNormSq (fun n ↦
        bVec B V S hgen hsymm n a -
          (w n - adFlat (B.map n (iota a) :
            Matrix (B.model n) (B.model n) ℂ) (w n))) =
      seqNormSq (fun n ↦
        CollapseWordMetric.bVec B V S n a -
          (w n - adFlat (B.map n (iota a) :
            Matrix (B.model n) (B.model n) ℂ) (w n))) := by
  refine seqNormSq_congr_of_eventually_eq
    (xdiff_bounded B iota V S hgen hsymm hVinv hVcomm hwbdd a)
    (xdiff_bounded_printed B iota k V S hgen hsymm hVinv hVcomm hVconv
      hwbdd a) ?_
  obtain ⟨N, hN⟩ := CollapseWordMetricBridge.eventually_profile_bVec_eq B iota
    k V S hgen hsymm hVinv hVcomm hVconv a
  exact ⟨N, fun n hn ↦ by rw [hN n hn]⟩

/-- **The compressed movers have exact primitives in the limit**: for an
orbit-fixed mover, the coboundary difference inherits the full
coboundary bound. -/
theorem compressed_primitive_limit {Γ E : Type} [Group Γ] [Group E]
    (B : OpAlmostRepresentation E) (iota : Γ →* E) (k : E)
    (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ) (S : Finset Γ)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    {w : ∀ n, EuclideanSpace ℂ (B.model n × B.model n)}
    (hwbdd : IsBoundedSeq w)
    {δa : Γ} (hfixed : orbitElement iota k δa = k) {d₀ : ℝ}
    (hcob : seqNormSq (fun n ↦
      bVec B V S hgen hsymm n δa -
        (w n - adFlat (B.map n (iota δa) :
          Matrix (B.model n) (B.model n) ℂ) (w n))) ≤ d₀) :
    seqNormSq (fun n ↦
      w n - adFlat (B.map n (iota δa) :
        Matrix (B.model n) (B.model n) ℂ) (w n)) ≤ d₀ := by
  obtain ⟨N, hN⟩ := eventually_bVec_eq_zero_of_orbit_fixed B iota k V S
    hgen hsymm hVinv hVcomm hVconv hfixed
  have hbndy := ydiff_bounded B iota hwbdd δa
  have hbndny : IsBoundedSeq (fun n ↦
      -(w n - adFlat (B.map n (iota δa) :
        Matrix (B.model n) (B.model n) ℂ) (w n))) := by
    obtain ⟨Cy, hCy⟩ := id hbndy
    exact ⟨Cy, fun n ↦ by
      rw [norm_neg]
      exact hCy n⟩
  have heq : ∃ N, ∀ n ≥ N,
      -(w n - adFlat (B.map n (iota δa) :
        Matrix (B.model n) (B.model n) ℂ) (w n)) =
        bVec B V S hgen hsymm n δa -
          (w n - adFlat (B.map n (iota δa) :
            Matrix (B.model n) (B.model n) ℂ) (w n)) := by
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [hN n hn, zero_sub]
  calc
    seqNormSq (fun n ↦
        w n - adFlat (B.map n (iota δa) :
          Matrix (B.model n) (B.model n) ℂ) (w n)) =
        seqNormSq (fun n ↦
          -(w n - adFlat (B.map n (iota δa) :
            Matrix (B.model n) (B.model n) ℂ) (w n))) :=
      (seqNormSq_neg _).symm
    _ = seqNormSq (fun n ↦
        bVec B V S hgen hsymm n δa -
          (w n - adFlat (B.map n (iota δa) :
            Matrix (B.model n) (B.model n) ℂ) (w n))) :=
      seqNormSq_congr_of_eventually_eq hbndny
        (xdiff_bounded B iota V S hgen hsymm hVinv hVcomm hwbdd δa) heq
    _ ≤ d₀ := hcob

/-- **The compressed movers have exact primitives in the limit**, for the
**printed** displacement vector of Step 4: at an orbit-fixed mover the
coboundary difference inherits the full coboundary bound, because the printed
vector vanishes there at all large stages. -/
theorem compressed_primitive_limit_printed {Γ E : Type} [Group Γ] [Group E]
    (B : OpAlmostRepresentation E) (iota : Γ →* E) (k : E)
    (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ) (S : Finset Γ)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    {w : ∀ n, EuclideanSpace ℂ (B.model n × B.model n)}
    (hwbdd : IsBoundedSeq w)
    {δa : Γ} (hfixed : orbitElement iota k δa = k) {d₀ : ℝ}
    (hcob : seqNormSq (fun n ↦
      CollapseWordMetric.bVec B V S n δa -
        (w n - adFlat (B.map n (iota δa) :
          Matrix (B.model n) (B.model n) ℂ) (w n))) ≤ d₀) :
    seqNormSq (fun n ↦
      w n - adFlat (B.map n (iota δa) :
        Matrix (B.model n) (B.model n) ℂ) (w n)) ≤ d₀ := by
  obtain ⟨N, hN⟩ :=
    CollapsePrintedProfile.eventually_printed_bVec_eq_zero_of_orbit_fixed B
      iota k V S hgen hsymm hVinv hVcomm hVconv hfixed
  have hbndy := ydiff_bounded B iota hwbdd δa
  have hbndny : IsBoundedSeq (fun n ↦
      -(w n - adFlat (B.map n (iota δa) :
        Matrix (B.model n) (B.model n) ℂ) (w n))) := by
    obtain ⟨Cy, hCy⟩ := id hbndy
    exact ⟨Cy, fun n ↦ by
      rw [norm_neg]
      exact hCy n⟩
  have heq : ∃ N, ∀ n ≥ N,
      -(w n - adFlat (B.map n (iota δa) :
        Matrix (B.model n) (B.model n) ℂ) (w n)) =
        CollapseWordMetric.bVec B V S n δa -
          (w n - adFlat (B.map n (iota δa) :
            Matrix (B.model n) (B.model n) ℂ) (w n)) := by
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [hN n hn, zero_sub]
  calc
    seqNormSq (fun n ↦
        w n - adFlat (B.map n (iota δa) :
          Matrix (B.model n) (B.model n) ℂ) (w n)) =
        seqNormSq (fun n ↦
          -(w n - adFlat (B.map n (iota δa) :
            Matrix (B.model n) (B.model n) ℂ) (w n))) :=
      (seqNormSq_neg _).symm
    _ = seqNormSq (fun n ↦
        CollapseWordMetric.bVec B V S n δa -
          (w n - adFlat (B.map n (iota δa) :
            Matrix (B.model n) (B.model n) ℂ) (w n))) :=
      seqNormSq_congr_of_eventually_eq hbndny
        (xdiff_bounded_printed B iota k V S hgen hsymm hVinv hVcomm hVconv
          hwbdd δa) heq
    _ ≤ d₀ := hcob

/-- **Corner capture of the compressed primitive**, assembled from the
residual bound and the vector capture inequality. -/
theorem stage_capture {Γ E : Type} [Group Γ] [Group E]
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (S : Finset Γ) (hone : 1 ∈ S) {θ : ℝ} (hθ1 : θ < 1) (n₀ : ℕ)
    (Xu : Matrix (B.model n₀) (B.model n₀) ℂ) {Cw τ : ℝ}
    (hCwpos : 0 < Cw) (hτpos : 0 < τ)
    (hmassXu : Real.sqrt (ScaledKazhdanTransport.matMass Xu) ≤ Cw)
    (hXudisp : ∀ a ∈ S,
      Real.sqrt (ScaledKazhdanTransport.matMass
        (Xu - (B.map n₀ (C.iota a) :
            Matrix (B.model n₀) (B.model n₀) ℂ) *
          Xu * (B.map n₀ (C.iota a) :
            Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ)) ≤ 2 * τ) :
    MarkedCompressionVectorChain.vecMass
      ((1 - cornerProjection B C S θ n₀) *ᵥ gammaRowVec B n₀ Xu) ≤
        ((Cw + 1) * (2 * τ)) / (1 - θ) := by
  have hres := sqrt_residual_mass_le B C S hone n₀ Xu
    (by linarith [hτpos] : (0 : ℝ) ≤ 2 * τ) hXudisp
  exact index_capture B C S hone (θ := θ) hθ1 n₀ Xu
    hCwpos.le (by linarith [hτpos] : (0 : ℝ) < 2 * τ) hmassXu hres

/-- The final per-generator bound: a displacement close to a small
coboundary difference is itself small. -/
theorem stage_generator_bound {H : Type*} [NormedAddCommGroup H]
    {b y : H} {τ ρt m : ℝ}
    (h1a : ‖b - y‖ ≤ τ) (hyW : ‖y‖ ^ 2 = m) (hnum : m ≤ (ρt / 2) ^ 2)
    (hτle : τ ≤ ρt / 2) (hρtpos : 0 < ρt) : ‖b‖ ≤ ρt := by
  have hyle : ‖y‖ ≤ ρt / 2 := by
    nlinarith [norm_nonneg y, hyW, hnum, hρtpos.le]
  calc
    ‖b‖ = ‖(b - y) + y‖ := by rw [sub_add_cancel]
    _ ≤ ‖b - y‖ + ‖y‖ := norm_add_le _ _
    _ ≤ ρt := by linarith [h1a, hyle, hτle]


/-- **The anchor contradiction**: a family of at most `1/(√|S|+1)`-small
values cannot carry total squared mass four. -/
theorem anchor_contradiction :
    ∀ {Γ : Type} {S : Finset Γ} {g : Γ → ℝ}
      (_hgnn : ∀ a ∈ S, 0 ≤ g a) (_hganchor : ∑ a ∈ S, g a ^ 2 = 4)
      {ρt : ℝ} (_hρt : ρt = 1 / (Real.sqrt ((S.card : ℝ)) + 1))
      (_hfin : ∀ a ∈ S, g a ≤ ρt), False := by
  intro Γ S g hgnn hganchor ρt hρt hfin
  have hsn := Real.sqrt_nonneg ((S.card : ℝ))
  have hx1 : (0 : ℝ) < Real.sqrt ((S.card : ℝ)) + 1 := by linarith
  have hρtpos : 0 < ρt := by
    rw [hρt]
    exact one_div_pos.mpr hx1
  have hsum_le : ∑ a ∈ S, g a ^ 2 ≤ (S.card : ℝ) * ρt ^ 2 := by
    calc
      ∑ a ∈ S, g a ^ 2 ≤ ∑ _a ∈ S, ρt ^ 2 :=
        Finset.sum_le_sum fun a ha ↦ by
          nlinarith [hgnn a ha, hfin a ha, hρtpos.le]
      _ = (S.card : ℝ) * ρt ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hlt : (S.card : ℝ) * ρt ^ 2 < 4 := by
    rw [hρt]
    have hs : Real.sqrt ((S.card : ℝ)) ^ 2 = (S.card : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg _)
    have hx2pos : (0 : ℝ) < (Real.sqrt ((S.card : ℝ)) + 1) ^ 2 :=
      pow_pos hx1 2
    have hcnn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    rw [div_pow, one_pow, mul_one_div, div_lt_iff₀ hx2pos]
    nlinarith [hs, hsn, hcnn]
  linarith [hganchor, hsum_le, hlt]

/-- **One-stage corner transport of the primitive.**  Capture of the
compressed primitive by the Kazhdan corner, together with the corner
displacement and reverse-corner estimates, bounds the displacement of
the primitive itself by each generator. -/
theorem stage_transport_bound :
    ∀ {Γ E : Type} [Group Γ] [Group E]
      (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
      (S : Finset Γ) (θ : ℝ) (n₀ : ℕ) (a : Γ)
      {Us W Xu : Matrix (B.model n₀) (B.model n₀) ℂ}
      (_hUs : Us = (B.map n₀ C.t : Matrix (B.model n₀) (B.model n₀) ℂ))
      (_hUsmem : Us ∈ Matrix.unitaryGroup (B.model n₀) ℂ)
      (_hXu : Xu = Usᴴ * W * Us) {q κ Cw : ℝ}
      (_hfix : ‖(((gammaAdjoint B C).map n₀ a :
          Matrix (B.adjoint.model n₀) (B.adjoint.model n₀) ℂ) - 1) *
          cornerProjection B C S θ n₀‖ ≤ q)
      (_hrev : ‖((1 : Matrix (B.adjoint.model n₀)
          (B.adjoint.model n₀) ℂ) - cornerProjection B C S θ n₀) *
          movedProjection B C S θ n₀‖ ≤ q)
      (_hcap : MarkedCompressionVectorChain.vecMass
        ((1 - cornerProjection B C S θ n₀) *ᵥ gammaRowVec B n₀ Xu) ≤ κ)
      (_hXumass : ScaledKazhdanTransport.matMass Xu ≤ Cw ^ 2),
      ScaledKazhdanTransport.matMass
        (W - (B.map n₀ (C.iota a) : Matrix (B.model n₀) (B.model n₀) ℂ) *
          W * (B.map n₀ (C.iota a) :
            Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ) ≤
        18 * q ^ 2 * Cw ^ 2 + 16 * κ := by
  intro Γ E _ _ B C S θ n₀ a Us W Xu hUs hUsmem hXu q κ Cw hfix hrev hcap
    hXumass
  have hYcard : 0 < Fintype.card (B.adjoint.model n₀) :=
    B.adjoint.modelNonempty n₀
  have hP := cornerProjection_isOrthogonalProjection B C S θ n₀
  have hTmem : (B.adjoint.map n₀ C.t :
      Matrix (B.adjoint.model n₀) (B.adjoint.model n₀) ℂ) ∈
      Matrix.unitaryGroup (B.adjoint.model n₀) ℂ :=
    (B.adjoint.map n₀ C.t).2
  have hAmem : ((gammaAdjoint B C).map n₀ a :
      Matrix (B.adjoint.model n₀) (B.adjoint.model n₀) ℂ) ∈
      Matrix.unitaryGroup (B.adjoint.model n₀) ℂ :=
    ((gammaAdjoint B C).map n₀ a).2
  have hrev' : ‖((1 : Matrix (B.adjoint.model n₀)
      (B.adjoint.model n₀) ℂ) - cornerProjection B C S θ n₀) *
      ((B.adjoint.map n₀ C.t :
        Matrix (B.adjoint.model n₀) (B.adjoint.model n₀) ℂ) *
        cornerProjection B C S θ n₀ *
        (B.adjoint.map n₀ C.t :
          Matrix (B.adjoint.model n₀) (B.adjoint.model n₀) ℂ)ᴴ)‖ ≤
      q := by
    have h := hrev
    unfold movedProjection at h
    exact h
  have htrans := MarkedCompressionVectorChain.transported_displacement_le
    hYcard hP hTmem hAmem hfix hrev' hcap
  have hUsUsH : Us * Usᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hUsmem
    rwa [Matrix.star_eq_conjTranspose] at h
  have hWrecover : Us * Xu * Usᴴ = W := by
    rw [hXu]
    calc
      Us * (Usᴴ * W * Us) * Usᴴ = (Us * Usᴴ) * W * (Us * Usᴴ) := by
        noncomm_ring
      _ = W := by rw [hUsUsH, one_mul, mul_one]
  have hTx : (B.adjoint.map n₀ C.t :
      Matrix (B.adjoint.model n₀) (B.adjoint.model n₀) ℂ) *ᵥ
      gammaRowVec B n₀ Xu = gammaRowVec B n₀ W := by
    have h := KazhdanAsymptoticCommutant.adjointMatrixSequence_mulVec_gammaRowVec
      B (fun m ↦ B.map m C.t) n₀ Xu
    have hid : KazhdanAsymptoticCommutant.adjointMatrixSequence B
        (fun m ↦ B.map m C.t) n₀ =
        (B.adjoint.map n₀ C.t :
          Matrix (B.adjoint.model n₀) (B.adjoint.model n₀) ℂ) := rfl
    rw [hid] at h
    rw [h, ← hUs, hWrecover]
  have hAx : ((gammaAdjoint B C).map n₀ a :
      Matrix (B.adjoint.model n₀) (B.adjoint.model n₀) ℂ) *ᵥ
      gammaRowVec B n₀ W =
      gammaRowVec B n₀
        ((B.map n₀ (C.iota a) :
          Matrix (B.model n₀) (B.model n₀) ℂ) * W *
          (B.map n₀ (C.iota a) :
            Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ) :=
    gammaAdjoint_mulVec_gammaRowVec B C n₀ a W
  rw [hTx, hAx] at htrans
  have hvm : ∀ Z : Matrix (B.model n₀) (B.model n₀) ℂ,
      MarkedCompressionVectorChain.vecMass (gammaRowVec B n₀ Z) =
        ScaledKazhdanTransport.matMass Z := by
    intro Z
    show (∑ p : B.adjoint.model n₀,
      Complex.normSq (gammaRowVec B n₀ Z p)) = _
    rw [sum_normSq_gammaRowVec]
    rfl
  have hdiff : gammaRowVec B n₀
      ((B.map n₀ (C.iota a) : Matrix (B.model n₀) (B.model n₀) ℂ) * W *
        (B.map n₀ (C.iota a) :
          Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ) -
      gammaRowVec B n₀ W =
      gammaRowVec B n₀
        ((B.map n₀ (C.iota a) : Matrix (B.model n₀) (B.model n₀) ℂ) * W *
          (B.map n₀ (C.iota a) :
            Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ - W) := rfl
  rw [hdiff, hvm] at htrans
  rw [hvm Xu] at htrans
  have hflip : ScaledKazhdanTransport.matMass
      (W - (B.map n₀ (C.iota a) : Matrix (B.model n₀) (B.model n₀) ℂ) *
        W * (B.map n₀ (C.iota a) :
          Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ) =
      ScaledKazhdanTransport.matMass
        ((B.map n₀ (C.iota a) : Matrix (B.model n₀) (B.model n₀) ℂ) * W *
          (B.map n₀ (C.iota a) :
            Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ - W) := by
    rw [show W - (B.map n₀ (C.iota a) :
        Matrix (B.model n₀) (B.model n₀) ℂ) * W *
        (B.map n₀ (C.iota a) : Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ =
        -((B.map n₀ (C.iota a) : Matrix (B.model n₀) (B.model n₀) ℂ) * W *
          (B.map n₀ (C.iota a) :
            Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ - W) by abel,
      ScaledKazhdanTransport.matMass_neg]
  rw [hflip]
  have hq2nn : (0 : ℝ) ≤ q ^ 2 := sq_nonneg q
  have hmid : (2 * q ^ 2 + 16 * q ^ 2) *
      ScaledKazhdanTransport.matMass Xu ≤ 18 * q ^ 2 * Cw ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hXumass
      (by nlinarith [hq2nn] : (0 : ℝ) ≤ 2 * q ^ 2 + 16 * q ^ 2)
    nlinarith [h]
  linarith [htrans, hmid]

variable {Γ E : Type} [Group Γ] [Group E]

/-- **The marked-model contradiction.**  No operator-norm almost
representation of the ambient group can keep the collapse commutator
uniformly separated from the identity. -/
theorem no_marked_model [Countable Γ]
    (iota : Γ →* E) (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ)
    (s : E) (hcomp : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    {kk : E} (hk2 : kk * kk = 1)
    (horb : ∀ γ₁ γ₂ : Γ,
      orbitElement iota kk γ₁ * orbitElement iota kk γ₂ =
        orbitElement iota kk γ₂ * orbitElement iota kk γ₁)
    (hH : ∀ γ : Γ, (s * iota γ * s⁻¹) * kk = kk * (s * iota γ * s⁻¹))
    (γ₀ : Γ)
    (M : MarkedOpAlmostRepresentation E ⁅iota γ₀, kk⁆) : False := by
  classical
  set B := M.toOpAlmostRepresentation with hB
  -- corrected involution microstates
  obtain ⟨V, hVinv, hVcomm, hVconv⟩ :=
    exists_involutionMicrostates B iota hk2 horb
  -- a symmetric generating Kazhdan pair
  obtain ⟨S, κ, _hone, hsymm, hgen, _hκpos, _hκ1, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair
      hkazhdan
  -- the marked separation forces the mass anchor
  have hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n :=
    eventually_one_le_kNorm_of_marked B iota kk V S hgen hsymm hVinv
      hVcomm hVconv (k2 := hk2) (γ₀ := γ₀) M.separation_pos
      M.marked_separated
  -- the limiting displacement profile is bounded **by its generator values**:
  -- the Delorme estimate of `rem:collapse-finite-stage`, read on the limiting
  -- cocycle with the mass identity `eq:generator-mass`, gives a bound
  -- depending on the Kazhdan pair alone
  set R : ℝ := 111 / κ ^ 2 with hRdef
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    exact div_nonneg (by norm_num) (sq_nonneg κ)
  -- read on the printed displacement vector of Step 4
  have hR : ∀ γ : Γ,
      seqNormSq (fun n ↦ CollapseWordMetric.bVec B V S n γ) ≤ R := by
    intro γ
    rw [hRdef]
    exact CollapsePrintedProfile.printed_profile_le_num B iota kk V S hgen
      hsymm hVinv hVcomm hVconv hmark hpair γ
  -- the compressed conjugates
  set da : Γ → Γ := fun a ↦ Classical.choose (hcomp a) with hdadef
  have hda : ∀ a : Γ, s * iota a * s⁻¹ = iota (da a) :=
    fun a ↦ Classical.choose_spec (hcomp a)
  -- (W2) makes the compressed conjugates fix the witness
  have hfixda : ∀ a : Γ, orbitElement iota kk (da a) = kk := by
    intro a
    show iota (da a) * kk * (iota (da a))⁻¹ = kk
    have hx : iota (da a) * kk = kk * iota (da a) := by
      rw [← hda a]
      exact hH a
    calc
      iota (da a) * kk * (iota (da a))⁻¹ =
          kk * iota (da a) * (iota (da a))⁻¹ := by rw [hx]
      _ = kk := by group
  -- the anchor threshold
  set ρt : ℝ := 1 / (Real.sqrt (S.card : ℝ) + 1) with hρt
  have hρtpos : 0 < ρt := by
    rw [hρt]
    have hx : (0 : ℝ) < Real.sqrt ((S.card : ℝ)) + 1 := by
      have := Real.sqrt_nonneg ((S.card : ℝ))
      linarith
    exact one_div_pos.mpr hx
  -- Step 6, through the weighted transport theorem at the rank weight
  obtain ⟨n₀, hkpos, hfinal⟩ :=
    CollapseTransportEndpoint.exists_stage_generators_small B iota kk V S hgen
      hsymm hVinv hVcomm hVconv hmark hR0 hR hkazhdan s hcomp da hda hfixda
      hρtpos
  -- the anchor contradiction, against `eq:generator-mass` for the printed
  -- displacement vector
  have hkpos' : 0 < kNorm B V S n₀ := lt_of_lt_of_le Nat.zero_lt_one hkpos
  have hanchor := CollapseWordMetric.col21_sum_normSq_bVec_eq_four B V S
    hVinv hVcomm hkpos'
  exact anchor_contradiction (fun a _ ↦ norm_nonneg _) hanchor hρt
    hfinal

/-! ## The corona-level collapse -/

/-- **The unconditional corona collapse**, sequence-quotient form: every
unitary-sequence corona representation of the ambient group kills the
collapse commutator. -/
theorem coronaMFInvisible_commutator [Countable Γ] [Countable E]
    (iota : Γ →* E) (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ)
    (s : E) (hcomp : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    {kk : E} (hk2 : kk * kk = 1)
    (horb : ∀ γ₁ γ₂ : Γ,
      orbitElement iota kk γ₁ * orbitElement iota kk γ₂ =
        orbitElement iota kk γ₂ * orbitElement iota kk γ₁)
    (hH : ∀ γ : Γ, (s * iota γ * s⁻¹) * kk = kk * (s * iota γ * s⁻¹))
    (γ₀ : Γ) :
    CoronaMFInvisible ⁅iota γ₀, kk⁆ := by
  intro X _hX rho
  by_contra hz
  obtain ⟨M⟩ :=
    exists_markedOpAlmostRepresentation_of_normMatrixCorona_ne_one
      X rho hz
  exact no_marked_model iota hkazhdan s hcomp hk2 horb hH γ₀ M

/-- **The unconditional corona collapse.**  Every norm matrix C*-corona
representation of the ambient group kills the collapse commutator: no
hypothesis beyond the group theory of the compression data. -/
theorem actualCoronaMFInvisible_commutator [Countable Γ] [Countable E]
    (iota : Γ →* E) (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ)
    (s : E) (hcomp : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    {kk : E} (hk2 : kk * kk = 1)
    (horb : ∀ γ₁ γ₂ : Γ,
      orbitElement iota kk γ₁ * orbitElement iota kk γ₂ =
        orbitElement iota kk γ₂ * orbitElement iota kk γ₁)
    (hH : ∀ γ : Γ, (s * iota γ * s⁻¹) * kk = kk * (s * iota γ * s⁻¹))
    (γ₀ : Γ) :
    ActualCoronaMFInvisible ⁅iota γ₀, kk⁆ :=
  actualCoronaMFInvisible_iff_coronaMFInvisible.mpr
    (coronaMFInvisible_commutator iota hkazhdan s hcomp hk2 horb hH γ₀)

/-! ## Discharge of the involutive compression-collapse endpoints -/

section InvolutiveDischarge

open TorsionCompressionCollapse

variable {E : Type} [Group E]

/- Quotients of countable groups are countable.  Proved once as
`GroupApproximation.CountableInstances.quotientCountable` and taken here with
the same `local` scope the mirrored copy had. -/
attribute [local instance] GroupApproximation.CountableInstances.quotientCountable

/-- An involutive torsion compression witness: an involution centralized
by the `s`-compressed copy of `L` whose `L`-conjugation orbit commutes
pairwise. -/
def IsInvolutiveCompressionWitness (L : Subgroup E) (s : E) (k : E) :
    Prop :=
  k * k = 1 ∧ (∀ γ ∈ L, Commute (s * γ * s⁻¹) k) ∧
    (∀ γ₁ ∈ L, ∀ γ₂ ∈ L, Commute (γ₁ * k * γ₁⁻¹) (γ₂ * k * γ₂⁻¹))

/-- Involutive witnesses are torsion compression witnesses. -/
theorem IsInvolutiveCompressionWitness.isTorsionCompressionWitness
    {L : Subgroup E} {s k : E}
    (hk : IsInvolutiveCompressionWitness L s k) :
    IsTorsionCompressionWitness L s k :=
  ⟨⟨2, two_pos, by rw [pow_two]; exact hk.1⟩, hk.2.1, hk.2.2⟩

/-- **Unconditional collapse of involutive witnesses.**  For a countable
ambient group, a Kazhdan subgroup with a one-sided compressor, and an
involutive witness, every collapse commutator is invisible in every
corona representation.  This discharges the collapse hypothesis of the
compression-collapse endpoints for the involutive witness class. -/
theorem actualCoronaMFInvisible_of_involutiveWitness [Countable E]
    {L : Subgroup E} (hkazhdan : HasKazhdanPropertyT.{0, 0} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    {k : E} (hk : IsInvolutiveCompressionWitness L s k)
    {γ : E} (hγ : γ ∈ L) :
    ActualCoronaMFInvisible ⁅γ, k⁆ := by
  have horb : ∀ γ₁ γ₂ : ↥L,
      orbitElement L.subtype k γ₁ * orbitElement L.subtype k γ₂ =
        orbitElement L.subtype k γ₂ * orbitElement L.subtype k γ₁ := by
    intro γ₁ γ₂
    exact (hk.2.2 (γ₁ : E) γ₁.2 (γ₂ : E) γ₂.2).eq
  have hH : ∀ γ' : ↥L,
      (s * L.subtype γ' * s⁻¹) * k = k * (s * L.subtype γ' * s⁻¹) :=
    fun γ' ↦ (hk.2.1 (γ' : E) γ'.2).eq
  have hcomp' : ∀ γ' : ↥L, ∃ δ : ↥L,
      s * L.subtype γ' * s⁻¹ = L.subtype δ :=
    fun γ' ↦ ⟨⟨s * (γ' : E) * s⁻¹, hcomp (γ' : E) γ'.2⟩, rfl⟩
  exact actualCoronaMFInvisible_commutator L.subtype hkazhdan s hcomp'
    hk.1 horb hH ⟨γ, hγ⟩

/-- The marked collapse commutators of all involutive witnesses. -/
def involutiveCollapseSet (L : Subgroup E) (s : E) : Set E :=
  {x | ∃ k : E, IsInvolutiveCompressionWitness L s k ∧
    ∃ γ ∈ L, x = ⁅γ, k⁆}

/-- The intrinsic involutive compression-collapse defect subgroup. -/
def involutiveCollapseDefect (L : Subgroup E) (s : E) : Subgroup E :=
  Subgroup.normalClosure (involutiveCollapseSet L s)

instance involutiveCollapseDefect_normal (L : Subgroup E) (s : E) :
    (involutiveCollapseDefect L s).Normal :=
  Subgroup.normalClosure_normal

/-- **Unconditional radical membership.**  The involutive collapse defect
of a Kazhdan subgroup with a one-sided compressor lies in the literal MF
radical — no analytic hypothesis remains. -/
theorem involutiveCollapseDefect_le_actualCoronaMFResidual [Countable E]
    {L : Subgroup E} (hkazhdan : HasKazhdanPropertyT.{0, 0} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L) :
    involutiveCollapseDefect L s ≤ actualCoronaMFResidual E := by
  rw [involutiveCollapseDefect]
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨k, hk, γ, hγ, rfl⟩
  exact actualCoronaMFInvisible_of_involutiveWitness hkazhdan hcomp hk hγ

/-- **The exact MF radical.**  When the involutive defect quotient is
itself MF, the literal MF radical of the ambient group is computed
exactly by the involutive collapse defect.  Only the radical membership
half used analysis, and it is unconditional. -/
theorem actualCoronaMFResidual_eq_involutiveCollapseDefect [Countable E]
    {L : Subgroup E} (hkazhdan : HasKazhdanPropertyT.{0, 0} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (hquot : IsCDEOperatorMF (E ⧸ involutiveCollapseDefect L s)) :
    actualCoronaMFResidual E = involutiveCollapseDefect L s :=
  actualCoronaMFResidual_eq_of_le_and_quotient_isCDEOperatorMF
    (involutiveCollapseDefect L s)
    (involutiveCollapseDefect_le_actualCoronaMFResidual hkazhdan hcomp)
    hquot

/-- **Reduction of the universal MF quotient.**  Unconditionally, the MF
radical of the ambient group is the full preimage of the radical of the
involutive defect quotient. -/
theorem actualCoronaMFResidual_eq_comap_involutive_quotient [Countable E]
    {L : Subgroup E} (hkazhdan : HasKazhdanPropertyT.{0, 0} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L) :
    actualCoronaMFResidual E =
      (actualCoronaMFResidual (E ⧸ involutiveCollapseDefect L s)).comap
        (QuotientGroup.mk' (involutiveCollapseDefect L s)) :=
  actualCoronaMFResidual_eq_comap_quotient _
    (involutiveCollapseDefect_le_actualCoronaMFResidual hkazhdan hcomp)

end InvolutiveDischarge

end InvolutionCollapseEndpoint
end GroupApproximation
