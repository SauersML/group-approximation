import GroupApproximation.Sofic.InvolutionCollapseEndpointPrep
import GroupApproximation.Sofic.TorsionCompressionCollapse

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
ultralimit Gaussian boundedness of the displacement profile
(`Kazhdan.UltralimitGaussianBoundedness`), one approximate coboundary
primitive from sequence-level circumcenters (`…Center`), and a one-stage
Kazhdan corner transport (`…IndexCapture`) that contradicts the
nonvanishing mass anchor of a marked model.
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

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

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
  obtain ⟨S, κ, hone, hsymm, hgen, hκpos, hκ1, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair
      hkazhdan
  have hcardR : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
  -- the marked separation forces the mass anchor
  have hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n :=
    eventually_one_le_kNorm_of_marked B iota kk V S hgen hsymm hVinv
      hVcomm hVconv (k2 := hk2) (γ₀ := γ₀) M.separation_pos
      M.marked_separated
  -- the displacement profile is uniformly bounded
  have hbdd : ∀ g : Γ, ∃ C : ℝ, ∀ n,
      ‖bVec B V S hgen hsymm n g‖ ^ 2 ≤ C :=
    fun g ↦ ⟨4 * (wordLen S hgen hsymm g : ℝ),
      fun n ↦ norm_bVec_sq_le B V S hgen hsymm hVinv hVcomm n g⟩
  obtain ⟨R₀, hR₀⟩ := UltralimitGaussian.profile_bounded_of_isKazhdanPair
    hpair hbdd (fun n ↦ bVec_one B V S hgen hsymm n)
    (profile_halmost B iota kk V S hgen hsymm hVinv hVcomm hVconv hmark)
  set R : ℝ := max R₀ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : ∀ γ : Γ, seqNormSq (fun n ↦ bVec B V S hgen hsymm n γ) ≤ R :=
    fun γ ↦ le_trans (hR₀ γ) (le_max_left _ _)
  -- the compression core for the corner machinery
  set C : KazhdanCompressionCore Γ E :=
    { iota := iota
      t := s
      c := 1
      kazhdan := hkazhdan
      compresses := hcomp
      comm_c := fun γ ↦ Commute.one_left _ } with hC
  -- the compressed conjugates
  set da : Γ → Γ := fun a ↦ Classical.choose (hcomp a) with hdadef
  have hda : ∀ a : Γ, s * iota a * s⁻¹ = iota (da a) :=
    fun a ↦ Classical.choose_spec (hcomp a)
  -- explicit constants
  set Cw : ℝ := Real.sqrt R + 2 with hCw
  have hCwpos : 0 < Cw := by
    rw [hCw]
    have := Real.sqrt_nonneg R
    linarith
  have hCw1 : (0 : ℝ) < Cw + 1 := by linarith
  set ρt : ℝ := 1 / (Real.sqrt (S.card : ℝ) + 1) with hρt
  have hρtpos : 0 < ρt := by
    rw [hρt]
    have hx : (0 : ℝ) < Real.sqrt ((S.card : ℝ)) + 1 := by
      have := Real.sqrt_nonneg ((S.card : ℝ))
      linarith
    exact one_div_pos.mpr hx
  set θ : ℝ := (1 - κ ^ 2 / (4 * (S.card : ℝ)) + 1) / 2 with hθdef
  have h4c : (0 : ℝ) < 4 * (S.card : ℝ) := by nlinarith [hcardR]
  have hκ2 : 0 < κ ^ 2 / (4 * (S.card : ℝ)) :=
    div_pos (pow_pos hκpos 2) h4c
  have hθ4 : 1 - κ ^ 2 / (4 * (S.card : ℝ)) < θ := by
    rw [hθdef]
    linarith
  have hθ1 : θ < 1 := by
    rw [hθdef]
    linarith
  have hgap : 0 < 1 - θ := by linarith
  set τ : ℝ := min (ρt / 2)
    ((1 - θ) * ρt ^ 2 / (256 * (Cw + 1))) with hτdef
  have hτpos : 0 < τ :=
    lt_min (half_pos hρtpos)
      (div_pos (mul_pos hgap (pow_pos hρtpos 2)) (by nlinarith [hCwpos]))
  set q : ℝ := ρt / (24 * (Cw + 1)) with hqdef
  have hqpos : 0 < q := div_pos hρtpos (by nlinarith [hCwpos])
  set d₀ : ℝ := τ ^ 2 / 2 with hd0def
  have hd0pos : 0 < d₀ := div_pos (pow_pos hτpos 2) two_pos
  set ε₆ : ℝ := τ / (2 * Cw + 2) with hε6def
  have hε6pos : 0 < ε₆ := div_pos hτpos (by nlinarith [hCwpos])
  have hsqrt2d : Real.sqrt (2 * d₀) = τ := by
    rw [hd0def, show 2 * (τ ^ 2 / 2) = τ ^ 2 by ring]
    exact Real.sqrt_sq hτpos.le
  -- the approximate coboundary primitive
  set T : Finset Γ := S ∪ S.image da with hTdef
  obtain ⟨w, hwbdd, hwnorm, hwcob⟩ :=
    exists_approximate_coboundary B iota kk V S hgen hsymm hVinv hVcomm
      hVconv hmark hR0 hR T hd0pos
  -- boundedness of the coboundary differences
  have hydiffbdd : ∀ a : Γ, IsBoundedSeq (fun n ↦
      w n - adFlat (B.map n (iota a) :
        Matrix (B.model n) (B.model n) ℂ) (w n)) := by
    intro a
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
  have hxdiffbdd : ∀ a : Γ, IsBoundedSeq (fun n ↦
      bVec B V S hgen hsymm n a -
        (w n - adFlat (B.map n (iota a) :
          Matrix (B.model n) (B.model n) ℂ) (w n))) := by
    intro a
    obtain ⟨Ca, hCa⟩ :=
      id (isBoundedSeq_bVec B V S hgen hsymm hVinv hVcomm a)
    obtain ⟨Cy, hCy⟩ := id (hydiffbdd a)
    refine ⟨Ca + Cy, fun n ↦ ?_⟩
    calc
      ‖bVec B V S hgen hsymm n a -
          (w n - adFlat (B.map n (iota a) :
            Matrix (B.model n) (B.model n) ℂ) (w n))‖ ≤
          ‖bVec B V S hgen hsymm n a‖ +
            ‖w n - adFlat (B.map n (iota a) :
              Matrix (B.model n) (B.model n) ℂ) (w n)‖ := norm_sub_le _ _
      _ ≤ Ca + Cy := add_le_add (hCa n) (hCy n)
  -- the compressed movers have exact primitives in the limit
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
  have hwda : ∀ a ∈ S, seqNormSq (fun n ↦
      w n - adFlat (B.map n (iota (da a)) :
        Matrix (B.model n) (B.model n) ℂ) (w n)) ≤ d₀ := by
    intro a haS
    have hmem : da a ∈ T := by
      rw [hTdef]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem da haS)
    have hcob := hwcob (da a) hmem
    obtain ⟨N, hN⟩ := eventually_bVec_eq_zero_of_orbit_fixed B iota kk V S
      hgen hsymm hVinv hVcomm hVconv (hfixda a)
    have hbndy := hydiffbdd (da a)
    have hbndny : IsBoundedSeq (fun n ↦
        -(w n - adFlat (B.map n (iota (da a)) :
          Matrix (B.model n) (B.model n) ℂ) (w n))) := by
      obtain ⟨Cy, hCy⟩ := id hbndy
      exact ⟨Cy, fun n ↦ by
        rw [norm_neg]
        exact hCy n⟩
    have heq : ∃ N, ∀ n ≥ N,
        -(w n - adFlat (B.map n (iota (da a)) :
          Matrix (B.model n) (B.model n) ℂ) (w n)) =
          bVec B V S hgen hsymm n (da a) -
            (w n - adFlat (B.map n (iota (da a)) :
              Matrix (B.model n) (B.model n) ℂ) (w n)) := by
      refine ⟨N, fun n hn ↦ ?_⟩
      rw [hN n hn, zero_sub]
    calc
      seqNormSq (fun n ↦
          w n - adFlat (B.map n (iota (da a)) :
            Matrix (B.model n) (B.model n) ℂ) (w n)) =
          seqNormSq (fun n ↦
            -(w n - adFlat (B.map n (iota (da a)) :
              Matrix (B.model n) (B.model n) ℂ) (w n))) :=
        (seqNormSq_neg _).symm
      _ = seqNormSq (fun n ↦
          bVec B V S hgen hsymm n (da a) -
            (w n - adFlat (B.map n (iota (da a)) :
              Matrix (B.model n) (B.model n) ℂ) (w n))) :=
        seqNormSq_congr_of_eventually_eq hbndny (hxdiffbdd (da a)) heq
      _ ≤ d₀ := hcob
  -- the hyperfilter-large stage set
  have hE1 : ∀ᶠ n in ↑(Filter.hyperfilter ℕ), ∀ a ∈ S,
      ‖bVec B V S hgen hsymm n a -
        (w n - adFlat (B.map n (iota a) :
          Matrix (B.model n) (B.model n) ℂ) (w n))‖ ≤ τ := by
    rw [Filter.eventually_all_finset]
    intro a haS
    have hcob := hwcob a (by
      rw [hTdef]
      exact Finset.mem_union_left _ haS)
    have h := eventually_norm_le_of_seqNormSq_le (hxdiffbdd a) hcob hd0pos
    rwa [hsqrt2d] at h
  have hE2 : ∀ᶠ n in ↑(Filter.hyperfilter ℕ), ∀ a ∈ S,
      ‖w n - adFlat (B.map n (iota (da a)) :
        Matrix (B.model n) (B.model n) ℂ) (w n)‖ ≤ τ := by
    rw [Filter.eventually_all_finset]
    intro a haS
    have h := eventually_norm_le_of_seqNormSq_le (hydiffbdd (da a))
      (hwda a haS) hd0pos
    rwa [hsqrt2d] at h
  have hE3 : ∀ᶠ n in ↑(Filter.hyperfilter ℕ), ‖w n‖ ≤ Cw := by
    have hlt : seqNorm w < Cw := by
      rw [hCw]
      linarith [hwnorm]
    filter_upwards [eventually_norm_lt_of_seqNorm_lt hwbdd hlt] with n hn
    exact hn.le
  have hE4 : ∀ᶠ n in ↑(Filter.hyperfilter ℕ), 1 ≤ kNorm B V S n :=
    hyperfilter_eventually_of_exists hmark
  have hE5 : ∀ᶠ n in ↑(Filter.hyperfilter ℕ), ∀ a ∈ S,
      ‖((gammaAdjoint B C).map n a -
          (1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)) *
        cornerProjection B C S θ n‖ ≤ q := by
    rw [Filter.eventually_all_finset]
    intro a haS
    exact hyperfilter_eventually_of_exists
      (displacement_vanishing B C θ hpair hone hκ1 hsymm hgen hθ4 a
        q hqpos)
  have hE6 : ∀ᶠ n in ↑(Filter.hyperfilter ℕ),
      ‖((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
          cornerProjection B C S θ n) * movedProjection B C S θ n‖ ≤ q :=
    hyperfilter_eventually_of_exists
      (one_sub_corner_mul_moved_vanishing B C θ hpair hone hκ1 hsymm
        hgen hθ4 hθ1 q hqpos)
  have hE7 : ∀ᶠ n in ↑(Filter.hyperfilter ℕ), ∀ a ∈ S,
      ‖(B.map n (iota a) : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n s : Matrix (B.model n) (B.model n) ℂ)ᴴ -
        (B.map n s : Matrix (B.model n) (B.model n) ℂ)ᴴ *
          B.map n (iota (da a))‖ ≤ ε₆ := by
    rw [Filter.eventually_all_finset]
    intro a haS
    exact hyperfilter_eventually_of_exists
      (mixed_conj_defect_vanishing B iota s (hda a) ε₆ hε6pos)
  obtain ⟨n₀, h1, h2, h3, h4, h5, h6, h7⟩ :=
    (hE1.and (hE2.and (hE3.and (hE4.and (hE5.and (hE6.and hE7)))))).exists
  -- the stage-n₀ transport
  set Us : Matrix (B.model n₀) (B.model n₀) ℂ :=
    (B.map n₀ s : Matrix (B.model n₀) (B.model n₀) ℂ) with hUs
  have hUsmem : Us ∈ Matrix.unitaryGroup (B.model n₀) ℂ := (B.map n₀ s).2
  set W : Matrix (B.model n₀) (B.model n₀) ℂ := unflatE (w n₀) with hW
  set Xu : Matrix (B.model n₀) (B.model n₀) ℂ := Usᴴ * W * Us with hXu
  have hmassWval : ScaledKazhdanTransport.matMass W = ‖w n₀‖ ^ 2 := by
    rw [← norm_flatE_sq, hW, flatE_unflatE]
  have hmassW : Real.sqrt (ScaledKazhdanTransport.matMass W) ≤ Cw := by
    rw [hmassWval, Real.sqrt_sq (norm_nonneg _)]
    exact h3
  have hmassXuW : ScaledKazhdanTransport.matMass Xu =
      ScaledKazhdanTransport.matMass W := by
    have h := ScaledKazhdanTransport.matMass_unitary_conj
      (conjTranspose_mem_unitaryGroup hUsmem) W
    rw [Matrix.conjTranspose_conjTranspose] at h
    rw [hXu]
    exact h
  have hmassXu : Real.sqrt (ScaledKazhdanTransport.matMass Xu) ≤ Cw := by
    rw [hmassXuW]
    exact hmassW
  -- the flat bridge between coboundary differences and matrix masses
  have hbridge : ∀ (U : Matrix (B.model n₀) (B.model n₀) ℂ),
      ‖w n₀ - adFlat U (w n₀)‖ ^ 2 =
        ScaledKazhdanTransport.matMass (W - U * W * Uᴴ) := by
    intro U
    have hflat : w n₀ - adFlat U (w n₀) = flatE (W - U * W * Uᴴ) := by
      rw [flatE_sub, hW, flatE_unflatE]
      rfl
    rw [hflat, norm_flatE_sq]
  -- per-generator displacement of the compressed matrix
  have hXudisp : ∀ a ∈ S,
      Real.sqrt (ScaledKazhdanTransport.matMass
        (Xu - (B.map n₀ (iota a) : Matrix (B.model n₀) (B.model n₀) ℂ) *
          Xu * (B.map n₀ (iota a) :
            Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ)) ≤ 2 * τ := by
    intro a haS
    set Ua : Matrix (B.model n₀) (B.model n₀) ℂ :=
      (B.map n₀ (iota a) : Matrix (B.model n₀) (B.model n₀) ℂ) with hUa
    set Ud : Matrix (B.model n₀) (B.model n₀) ℂ :=
      (B.map n₀ (iota (da a)) :
        Matrix (B.model n₀) (B.model n₀) ℂ) with hUd
    have hUamem : Ua ∈ Matrix.unitaryGroup (B.model n₀) ℂ :=
      (B.map n₀ (iota a)).2
    have hUdmem : Ud ∈ Matrix.unitaryGroup (B.model n₀) ℂ :=
      (B.map n₀ (iota (da a))).2
    have hsplit : Xu - Ua * Xu * Uaᴴ =
        Usᴴ * (W - Ud * W * Udᴴ) * Us +
          ((Usᴴ * Ud) * W * (Usᴴ * Ud)ᴴ -
            (Ua * Usᴴ) * W * (Ua * Usᴴ)ᴴ) := by
      rw [hXu]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      noncomm_ring
    have hflatnorm : ∀ Z : Matrix (B.model n₀) (B.model n₀) ℂ,
        ‖flatE Z‖ = Real.sqrt (ScaledKazhdanTransport.matMass Z) := by
      intro Z
      rw [← Real.sqrt_sq (norm_nonneg (flatE Z)), norm_flatE_sq]
    have hterm1 : Real.sqrt (ScaledKazhdanTransport.matMass
        (Usᴴ * (W - Ud * W * Udᴴ) * Us)) ≤ τ := by
      have hconj := ScaledKazhdanTransport.matMass_unitary_conj
        (conjTranspose_mem_unitaryGroup hUsmem) (W - Ud * W * Udᴴ)
      rw [Matrix.conjTranspose_conjTranspose] at hconj
      rw [hconj, ← hbridge Ud, Real.sqrt_sq (norm_nonneg _)]
      exact h2 a haS
    have hA12 : ‖(Usᴴ * Ud) - (Ua * Usᴴ)‖ ≤ ε₆ := by
      rw [norm_sub_rev]
      exact h7 a haS
    have hterm2 : Real.sqrt (ScaledKazhdanTransport.matMass
        ((Usᴴ * Ud) * W * (Usᴴ * Ud)ᴴ -
          (Ua * Usᴴ) * W * (Ua * Usᴴ)ᴴ)) ≤ 2 * (ε₆ * Cw) := by
      set A₁ : Matrix (B.model n₀) (B.model n₀) ℂ := Usᴴ * Ud with hA₁
      set A₂ : Matrix (B.model n₀) (B.model n₀) ℂ := Ua * Usᴴ with hA₂
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
            have hmw : ScaledKazhdanTransport.matMass W ≤ Cw ^ 2 := by
              rw [hmassWval]
              nlinarith [h3, norm_nonneg (w n₀)]
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
            have hmw : ScaledKazhdanTransport.matMass W ≤ Cw ^ 2 := by
              rw [hmassWval]
              nlinarith [h3, norm_nonneg (w n₀)]
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
    have hε6Cw : ε₆ * Cw ≤ τ / 2 := by
      rw [hε6def]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by nlinarith [hCwpos] :
        (0 : ℝ) < 2 * Cw + 2) (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hτpos.le, hCwpos]
    calc
      Real.sqrt (ScaledKazhdanTransport.matMass
          (Xu - Ua * Xu * Uaᴴ)) =
          ‖flatE (Xu - Ua * Xu * Uaᴴ)‖ := (hflatnorm _).symm
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
  -- capture of the compressed matrix by the Kazhdan corner
  have hres := sqrt_residual_mass_le B C S hone n₀ Xu
    (by linarith [hτpos] : (0 : ℝ) ≤ 2 * τ) hXudisp
  have hcap := index_capture B C S hone (θ := θ) hθ1 n₀ Xu
    hCwpos.le (by linarith [hτpos] : (0 : ℝ) < 2 * τ) hmassXu hres
  -- transported displacement of the primitive matrix
  have hvm : ∀ Z : Matrix (B.model n₀) (B.model n₀) ℂ,
      MarkedCompressionVectorChain.vecMass (gammaRowVec B n₀ Z) =
        ScaledKazhdanTransport.matMass Z := by
    intro Z
    show (∑ p : B.adjoint.model n₀,
      Complex.normSq (gammaRowVec B n₀ Z p)) = _
    rw [sum_normSq_gammaRowVec]
    rfl
  have hUsUsH : Us * Usᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hUsmem
    rwa [Matrix.star_eq_conjTranspose] at h
  have hWrecover : Us * Xu * Usᴴ = W := by
    rw [hXu]
    calc
      Us * (Usᴴ * W * Us) * Usᴴ = (Us * Usᴴ) * W * (Us * Usᴴ) := by
        noncomm_ring
      _ = W := by rw [hUsUsH, one_mul, mul_one]
  have hWdisp : ∀ a ∈ S,
      ScaledKazhdanTransport.matMass
        (W - (B.map n₀ (iota a) : Matrix (B.model n₀) (B.model n₀) ℂ) *
          W * (B.map n₀ (iota a) :
            Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ) ≤
        18 * q ^ 2 * Cw ^ 2 +
          16 * ((Cw + 1) * (2 * τ) / (1 - θ)) := by
    intro a haS
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
    have hfix : ‖(((gammaAdjoint B C).map n₀ a :
        Matrix (B.adjoint.model n₀) (B.adjoint.model n₀) ℂ) - 1) *
        cornerProjection B C S θ n₀‖ ≤ q := h5 a haS
    have hrev : ‖((1 : Matrix (B.adjoint.model n₀)
        (B.adjoint.model n₀) ℂ) - cornerProjection B C S θ n₀) *
        ((B.adjoint.map n₀ C.t :
          Matrix (B.adjoint.model n₀) (B.adjoint.model n₀) ℂ) *
          cornerProjection B C S θ n₀ *
          (B.adjoint.map n₀ C.t :
            Matrix (B.adjoint.model n₀) (B.adjoint.model n₀) ℂ)ᴴ)‖ ≤
        q := by
      have h := h6
      unfold movedProjection at h
      exact h
    have htrans := MarkedCompressionVectorChain.transported_displacement_le
      hYcard hP hTmem hAmem hfix hrev hcap
    -- identify the transported vector
    have hTx : (B.adjoint.map n₀ C.t :
        Matrix (B.adjoint.model n₀) (B.adjoint.model n₀) ℂ) *ᵥ
        gammaRowVec B n₀ Xu = gammaRowVec B n₀ W := by
      have h := KazhdanAsymptoticCommutant.adjointMatrixSequence_mulVec_gammaRowVec
        B (fun m ↦ B.map m s) n₀ Xu
      have hid : KazhdanAsymptoticCommutant.adjointMatrixSequence B
          (fun m ↦ B.map m s) n₀ =
          (B.adjoint.map n₀ C.t :
            Matrix (B.adjoint.model n₀) (B.adjoint.model n₀) ℂ) := rfl
      rw [hid] at h
      rw [h, ← hUs, hWrecover]
    have hAx : ((gammaAdjoint B C).map n₀ a :
        Matrix (B.adjoint.model n₀) (B.adjoint.model n₀) ℂ) *ᵥ
        gammaRowVec B n₀ W =
        gammaRowVec B n₀
          ((B.map n₀ (iota a) :
            Matrix (B.model n₀) (B.model n₀) ℂ) * W *
            (B.map n₀ (iota a) :
              Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ) :=
      gammaAdjoint_mulVec_gammaRowVec B C n₀ a W
    rw [hTx, hAx] at htrans
    have hdiff : gammaRowVec B n₀
        ((B.map n₀ (iota a) : Matrix (B.model n₀) (B.model n₀) ℂ) * W *
          (B.map n₀ (iota a) :
            Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ) -
        gammaRowVec B n₀ W =
        gammaRowVec B n₀
          ((B.map n₀ (iota a) : Matrix (B.model n₀) (B.model n₀) ℂ) * W *
            (B.map n₀ (iota a) :
              Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ - W) := rfl
    rw [hdiff, hvm] at htrans
    rw [hvm Xu] at htrans
    have hXumass : ScaledKazhdanTransport.matMass Xu ≤ Cw ^ 2 := by
      rw [hmassXuW, hmassWval]
      nlinarith [h3, norm_nonneg (w n₀)]
    have hflip : ScaledKazhdanTransport.matMass
        (W - (B.map n₀ (iota a) : Matrix (B.model n₀) (B.model n₀) ℂ) *
          W * (B.map n₀ (iota a) :
            Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ) =
        ScaledKazhdanTransport.matMass
          ((B.map n₀ (iota a) : Matrix (B.model n₀) (B.model n₀) ℂ) * W *
            (B.map n₀ (iota a) :
              Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ - W) := by
      rw [show W - (B.map n₀ (iota a) :
          Matrix (B.model n₀) (B.model n₀) ℂ) * W *
          (B.map n₀ (iota a) : Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ =
          -((B.map n₀ (iota a) : Matrix (B.model n₀) (B.model n₀) ℂ) * W *
            (B.map n₀ (iota a) :
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
  -- the numeric bound: transported mass is at most `(ρt / 2)²`
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
    have hτr : τ ≤ (1 - θ) * ρt ^ 2 / (256 * (Cw + 1)) :=
      min_le_right _ _
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
  -- per-generator stage bound
  have hfinal : ∀ a ∈ S, ‖bVec B V S hgen hsymm n₀ a‖ ≤ ρt := by
    intro a haS
    have h1a := h1 a haS
    have hyW := hbridge (B.map n₀ (iota a) :
      Matrix (B.model n₀) (B.model n₀) ℂ)
    have hWa := hWdisp a haS
    have hnum : ScaledKazhdanTransport.matMass
        (W - (B.map n₀ (iota a) : Matrix (B.model n₀) (B.model n₀) ℂ) *
          W * (B.map n₀ (iota a) :
            Matrix (B.model n₀) (B.model n₀) ℂ)ᴴ) ≤ (ρt / 2) ^ 2 := by
      have : (ρt / 2) ^ 2 = ρt ^ 2 / 4 := by ring
      rw [this]
      linarith [hA, hBnum, hWa]
    have hyle : ‖w n₀ - adFlat (B.map n₀ (iota a) :
        Matrix (B.model n₀) (B.model n₀) ℂ) (w n₀)‖ ≤ ρt / 2 := by
      have hnn := norm_nonneg (w n₀ - adFlat (B.map n₀ (iota a) :
        Matrix (B.model n₀) (B.model n₀) ℂ) (w n₀))
      nlinarith [hyW, hnum, hρtpos.le]
    have hτle : τ ≤ ρt / 2 := min_le_left _ _
    calc
      ‖bVec B V S hgen hsymm n₀ a‖ =
          ‖(bVec B V S hgen hsymm n₀ a -
            (w n₀ - adFlat (B.map n₀ (iota a) :
              Matrix (B.model n₀) (B.model n₀) ℂ) (w n₀))) +
            (w n₀ - adFlat (B.map n₀ (iota a) :
              Matrix (B.model n₀) (B.model n₀) ℂ) (w n₀))‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖bVec B V S hgen hsymm n₀ a -
            (w n₀ - adFlat (B.map n₀ (iota a) :
              Matrix (B.model n₀) (B.model n₀) ℂ) (w n₀))‖ +
          ‖w n₀ - adFlat (B.map n₀ (iota a) :
            Matrix (B.model n₀) (B.model n₀) ℂ) (w n₀)‖ :=
        norm_add_le _ _
      _ ≤ ρt := by linarith [h1a, hyle, hτle]
  -- the anchor contradiction
  have hkpos : 0 < kNorm B V S n₀ := lt_of_lt_of_le Nat.zero_lt_one h4
  have hanchor := sum_normSq_bVec_eq_four B V S hgen hsymm hVinv hVcomm
    hkpos
  have hsum_le : ∑ a ∈ S, ‖bVec B V S hgen hsymm n₀ a‖ ^ 2 ≤
      (S.card : ℝ) * ρt ^ 2 := by
    calc
      ∑ a ∈ S, ‖bVec B V S hgen hsymm n₀ a‖ ^ 2 ≤
          ∑ _a ∈ S, ρt ^ 2 :=
        Finset.sum_le_sum fun a ha ↦ by
          have := hfinal a ha
          nlinarith [norm_nonneg (bVec B V S hgen hsymm n₀ a), hρtpos.le]
      _ = (S.card : ℝ) * ρt ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hlt : (S.card : ℝ) * ρt ^ 2 < 4 := by
    rw [hρt]
    have hs : Real.sqrt ((S.card : ℝ)) ^ 2 = (S.card : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg _)
    have hsn := Real.sqrt_nonneg ((S.card : ℝ))
    have hx1 : (0 : ℝ) < Real.sqrt ((S.card : ℝ)) + 1 := by linarith
    have hx2pos : (0 : ℝ) < (Real.sqrt ((S.card : ℝ)) + 1) ^ 2 :=
      pow_pos hx1 2
    rw [div_pow, one_pow, mul_one_div, div_lt_iff₀ hx2pos]
    nlinarith [hs, hsn, hcardR]
  linarith [hanchor, hsum_le, hlt]

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

/-- Quotients of countable groups are countable; mirrored locally from
`Sofic.ActualCoronaMFRadical`, where the same instance is `local`. -/
local instance quotientCountable (N : Subgroup E) [hN : N.Normal]
    [Countable E] : Countable (E ⧸ N) :=
  Function.Surjective.countable
    (@QuotientGroup.mk'_surjective E _ N hN)

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
