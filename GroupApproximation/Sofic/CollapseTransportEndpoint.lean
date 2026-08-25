import GroupApproximation.Sofic.CollapsePrintedDiagonalization
import GroupApproximation.Sofic.CollapseScaledStepSix

/-!
# Step 6 of the involutive collapse, assembled through the transport theorem

This module supplies the single fact `no_marked_model` needs from Step 6: a
stage at which the printed displacement vector is small **at every Kazhdan
generator at once**, together with `k_n \ge 1` at that stage.  Against
`eq:generator-mass` — the generators carry total squared mass exactly four —
that is the contradiction.

What makes this the *transport* assembly rather than the one-stage one is that
the smallness is obtained by invoking
`ScaledKazhdanTransport.scaled_transport_both` at the rank weight `w_n = k_n`,
through `Sofic/CollapseScaledStepSix.lean`, instead of re-deriving a corner
estimate inline.  The divergence this route does *not* close is recorded in the
docstring of that module: `thm:collapse` Step 6 as printed transports inside the
Hilbert-space ultraproduct, which this development does not contain; what is
certified here is the rank-weight assertion the manuscript makes after
that weighted transport theorem.

The three inputs, all already proved:

* `CollapsePrintedDiagonalization.exists_cofinal_vanishing_coboundary_primitive_printed`
  — a cofinal reindexing `φ`, a primitive `W` bounded at every stage, and a
  coboundary defect below `2/(j+1)` at every stage, all against the printed
  `b_n` rather than the capped one;
* `CollapseTransportDiagonalization.isScaledMassBounded_rankScaled` and
  `scaledMassVanishing_rankScaled` — the two hypotheses of the transport
  theorem, at the weight `ρ j = k_{φ j}`, the second one holding at the
  *compressed* generators because `(W2)` makes the displacement vanish there;
* `CollapseScaledStepSix.scaledAsymptoticCommutant_of_conj_vanishing` — the
  transport itself, promoting the compressed copy `s\iota(\Gamma)s^{-1}` to all
  of `\iota(\Gamma)`.

Unwinding is arithmetic: at the weight, the displacement mass of the rescaled
primitive is `ρ j` times the squared norm of the unrescaled displacement, so
where `ρ j > 0` the weight divides out and the primitive itself is moved by at
most `ρt/2` by each generator; the coboundary defect contributes another
`ρt/2`; and the triangle inequality gives `ρt`.
-/

namespace GroupApproximation
namespace CollapseTransportEndpoint

open Matrix InvolutionOrbitMicrostates InvolutionRankMass
open InvolutionCollapseMetric InvolutionMicrostateTools
open InvolutionCollapseProfile InvolutionCollapseCocycle
open InvolutionCollapseEndpointPrep
open CollapseTransportDiagonalization CollapseScaledStepSix
open Ultralimit KazhdanCornerMatrices KazhdanCompressorCorner
open ScaledKazhdanTransport
open scoped Matrix.Norms.L2Operator

attribute [local instance] InnerProductSpace.complexToReal

variable {Γ E : Type} [Group Γ] [Group E]

/-- A nonnegative real whose square is bounded by the square of a positive real
is bounded by it. -/
theorem le_of_sq_le_sq {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c)
    (h : x ^ 2 ≤ c ^ 2) : x ≤ c := by
  nlinarith [h, hx, hc]

/-- **The transport route to Step 6.**  Under the collapse data there is a
stage at which the generator normalization is positive and the printed
displacement vector is at most `ρt` at every Kazhdan generator simultaneously.

The stage is produced by the rank-weight transport, not by a one-stage corner
estimate: `scaled_transport_both` at `w_n = k_n` makes the diagonalized
primitive an asymptotic commutant of the whole of `\iota(\Gamma)`, and the
generator bound is read off from that. -/
theorem exists_stage_generators_small
    (B : OpAlmostRepresentation E) (iota : Γ →* E) (kk : E)
    (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ) (S : Finset Γ)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota kk n γ))
    (hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n)
    {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ γ : Γ,
      seqNormSq (fun n ↦ CollapseWordMetric.bVec B V S n γ) ≤ R)
    (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ) (s : E)
    (hcomp : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (da : Γ → Γ) (hda : ∀ a : Γ, s * iota a * s⁻¹ = iota (da a))
    (hfix : ∀ a : Γ, orbitElement iota kk (da a) = kk)
    {ρt : ℝ} (hρt : 0 < ρt) :
    ∃ n : ℕ, 1 ≤ kNorm B V S n ∧
      ∀ a ∈ S, ‖CollapseWordMetric.bVec B V S n a‖ ≤ ρt := by
  classical
  -- the mover set: the generators and their compressed images
  set T : Finset Γ := S ∪ S.image da with hTdef
  -- the diagonalized primitive, against the printed displacement vector
  obtain ⟨φ, W, hφ, hWn, hWdef⟩ :=
    CollapsePrintedDiagonalization.exists_cofinal_vanishing_coboundary_primitive_printed
      B iota kk V S hgen hsymm hVinv hVcomm hVconv hmark hR0 hR T
  -- the reindexed model and the rank weight
  set B' : OpAlmostRepresentation E := B.reindex φ hφ with hB'def
  set ρ : ℕ → ℝ := fun j ↦ ((kNorm B V S (φ j) : ℕ) : ℝ) with hρdef
  have hρ : ∀ j, 0 ≤ ρ j := fun j ↦ Nat.cast_nonneg _
  -- the compression core; its projections reduce definitionally
  let C : KazhdanCompressionCore Γ E :=
    { iota := iota
      t := s
      c := 1
      kazhdan := hkazhdan
      compresses := hcomp
      comm_c := fun _ ↦ Commute.one_left _ }
  -- The rescaled primitive, *named at the reindexed model*.  `B'.model j` and
  -- `B.model (φ j)` are definitionally equal — `reindex_model` is `rfl` — but
  -- `unflatE (W j)` infers the latter while `B'.map j g` infers the former, and
  -- `HMul` is synthesized from the inferred types, not up to defeq.  Binding the
  -- family with a declared type makes every leaf below syntactically `B'`-typed.
  set X : ∀ j, Matrix (B'.model j) (B'.model j) ℂ :=
    fun j ↦ ((Real.sqrt (ρ j) : ℝ) : ℂ) • unflatE (W j) with hXdef
  -- the two hypotheses of the transport theorem, at the rank weight
  have hbound : IsScaledMassBounded B' ρ X := by
    rw [hXdef]
    exact isScaledMassBounded_rankScaled B' ρ hρ W hWn
  have hS' : ∀ a ∈ S, ScaledMassVanishing B' ρ (fun j ↦
      X j -
        (B'.map j (C.t * C.iota a * C.t⁻¹) :
            Matrix (B'.model j) (B'.model j) ℂ) * X j *
          (B'.map j (C.t * C.iota a * C.t⁻¹) :
            Matrix (B'.model j) (B'.model j) ℂ)ᴴ) := by
    intro a haS
    have hgeq : s * iota a * s⁻¹ = iota (da a) := hda a
    rw [show C.t * C.iota a * C.t⁻¹ = iota (da a) from hgeq, hXdef]
    -- `(W2)` makes the printed displacement vanish at the compressed generator
    have hb : ∃ N, ∀ j ≥ N,
        CollapseWordMetric.bVec B V S (φ j) (da a) = 0 := by
      obtain ⟨N, hN⟩ :=
        CollapsePrintedProfile.eventually_printed_bVec_eq_zero_of_orbit_fixed
          B iota kk V S hgen hsymm hVinv hVcomm hVconv (hfix a)
      exact ⟨N, fun j hj ↦ hN (φ j) (le_trans hj (hφ j))⟩
    have hmem : da a ∈ T := by
      rw [hTdef]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem da haS)
    exact scaledMassVanishing_rankScaled B' ρ hρ (iota (da a)) W
      (fun j ↦ CollapseWordMetric.bVec B V S (φ j) (da a)) hb
      (fun j ↦ hWdef (da a) hmem j)
  -- Step 6: the transport theorem, at the rank weight `w_n = k_n`
  have hcomm := scaledAsymptoticCommutant_of_conj_vanishing hρ C S hgen
    hbound hS'
  -- a common late stage
  have hεpos : (0 : ℝ) < (ρt / 2) ^ 2 := by positivity
  choose Na hNa using fun a : Γ ↦ hcomm a ((ρt / 2) ^ 2) hεpos
  obtain ⟨Jr, hJr⟩ := exists_level_two_div_le hεpos
  obtain ⟨Nm, hNm⟩ := hmark
  set j₀ : ℕ := max (S.sup Na) (max Jr Nm) with hj0def
  have hjJr : Jr ≤ j₀ := le_trans (le_max_left Jr Nm) (le_max_right _ _)
  have hjNm : Nm ≤ j₀ := le_trans (le_max_right Jr Nm) (le_max_right _ _)
  have hkpos : 1 ≤ kNorm B V S (φ j₀) :=
    hNm (φ j₀) (le_trans hjNm (hφ j₀))
  have hρpos : 0 < ρ j₀ := by
    -- `rw` leaves the beta-redex `(fun j ↦ ↑(kNorm …)) j₀`, which `mod_cast`
    -- cannot see through; `simp only` contracts it.
    simp only [hρdef]
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hkpos
  refine ⟨φ j₀, hkpos, fun a haS ↦ ?_⟩
  -- the primitive is barely moved by the generator
  have hmass := hNa a j₀
    (le_trans (Finset.le_sup (f := Na) haS) (le_max_left _ _))
  -- unfold the naming binder again: the calc below speaks of the rescaled
  -- primitive itself, not of `X`
  simp only [hXdef] at hmass
  -- `B'.map j₀ (C.iota a)` and `B.map (φ j₀) (iota a)` are definitionally the
  -- same unitary, but only the latter is syntactically what the diagonalization
  -- speaks about, and `linarith` compares atoms syntactically; so every bound
  -- below is stated in the latter form and `hmass` is consumed up to defeq.
  have hWsq : ‖W j₀ - adFlat (B.map (φ j₀) (iota a) :
      Matrix (B.model (φ j₀)) (B.model (φ j₀)) ℂ) (W j₀)‖ ^ 2 ≤
      (ρt / 2) ^ 2 := by
    refine le_of_mul_le_mul_right ?_ hρpos
    have hid : ρ j₀ * ‖W j₀ - adFlat (B.map (φ j₀) (iota a) :
          Matrix (B.model (φ j₀)) (B.model (φ j₀)) ℂ) (W j₀)‖ ^ 2 =
        matMass (((Real.sqrt (ρ j₀) : ℝ) : ℂ) • unflatE (W j₀) -
          (B.map (φ j₀) (iota a) :
              Matrix (B.model (φ j₀)) (B.model (φ j₀)) ℂ) *
            (((Real.sqrt (ρ j₀) : ℝ) : ℂ) • unflatE (W j₀)) *
            (B.map (φ j₀) (iota a) :
              Matrix (B.model (φ j₀)) (B.model (φ j₀)) ℂ)ᴴ) := by
      rw [matMass_smul_unflatE_displacement, Real.sq_sqrt (hρ j₀)]
    calc
      ‖W j₀ - adFlat (B.map (φ j₀) (iota a) :
            Matrix (B.model (φ j₀)) (B.model (φ j₀)) ℂ) (W j₀)‖ ^ 2 * ρ j₀ =
          ρ j₀ * ‖W j₀ - adFlat (B.map (φ j₀) (iota a) :
            Matrix (B.model (φ j₀)) (B.model (φ j₀)) ℂ) (W j₀)‖ ^ 2 :=
        mul_comm _ _
      _ = matMass (((Real.sqrt (ρ j₀) : ℝ) : ℂ) • unflatE (W j₀) -
            (B.map (φ j₀) (iota a) :
                Matrix (B.model (φ j₀)) (B.model (φ j₀)) ℂ) *
              (((Real.sqrt (ρ j₀) : ℝ) : ℂ) • unflatE (W j₀)) *
              (B.map (φ j₀) (iota a) :
                Matrix (B.model (φ j₀)) (B.model (φ j₀)) ℂ)ᴴ) := hid
      _ ≤ (ρt / 2) ^ 2 * ρ j₀ := hmass
  have hWsmall : ‖W j₀ - adFlat (B.map (φ j₀) (iota a) :
      Matrix (B.model (φ j₀)) (B.model (φ j₀)) ℂ) (W j₀)‖ ≤ ρt / 2 :=
    le_of_sq_le_sq (norm_nonneg _) (by linarith) hWsq
  -- and the coboundary defect at the generator is small at this level
  have hmemS : a ∈ T := by
    rw [hTdef]
    exact Finset.mem_union_left _ haS
  have hdefsq : ‖CollapseWordMetric.bVec B V S (φ j₀) a -
      (W j₀ - adFlat (B.map (φ j₀) (iota a) :
        Matrix (B.model (φ j₀)) (B.model (φ j₀)) ℂ) (W j₀))‖ ^ 2 ≤
      (ρt / 2) ^ 2 :=
    le_trans (hWdef a hmemS j₀) (hJr j₀ hjJr)
  have hdefsmall : ‖CollapseWordMetric.bVec B V S (φ j₀) a -
      (W j₀ - adFlat (B.map (φ j₀) (iota a) :
        Matrix (B.model (φ j₀)) (B.model (φ j₀)) ℂ) (W j₀))‖ ≤ ρt / 2 :=
    le_of_sq_le_sq (norm_nonneg _) (by linarith) hdefsq
  -- the triangle inequality closes it
  calc
    ‖CollapseWordMetric.bVec B V S (φ j₀) a‖ =
        ‖(CollapseWordMetric.bVec B V S (φ j₀) a -
            (W j₀ - adFlat (B.map (φ j₀) (iota a) :
              Matrix (B.model (φ j₀)) (B.model (φ j₀)) ℂ) (W j₀))) +
          (W j₀ - adFlat (B.map (φ j₀) (iota a) :
            Matrix (B.model (φ j₀)) (B.model (φ j₀)) ℂ) (W j₀))‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖CollapseWordMetric.bVec B V S (φ j₀) a -
          (W j₀ - adFlat (B.map (φ j₀) (iota a) :
            Matrix (B.model (φ j₀)) (B.model (φ j₀)) ℂ) (W j₀))‖ +
        ‖W j₀ - adFlat (B.map (φ j₀) (iota a) :
          Matrix (B.model (φ j₀)) (B.model (φ j₀)) ℂ) (W j₀)‖ :=
      norm_add_le _ _
    _ ≤ ρt := by linarith [hdefsmall, hWsmall]

end CollapseTransportEndpoint
end GroupApproximation
