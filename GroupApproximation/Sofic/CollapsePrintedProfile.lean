import GroupApproximation.Sofic.CollapseProfileBoundNumeric
import GroupApproximation.Sofic.CollapseWordMetricBridge
import GroupApproximation.Sofic.InvolutionCollapseEndpointPrep

/-!
# Steps 4 and 5 of `thm:collapse`, carried by the printed displacement vector

`non_mf_groups_exist.tex`, Theorem `thm:collapse`, Step 4 prints

`b_n(\gamma) = k_n^{-1/2}\bigl(V_n(\gamma) - V_n(1)\bigr)`

with no guard, bounds `\|b_n(\gamma)\|_{\mathrm F}^2 \le 4|\gamma|_S` **at every
large stage** against the genuine word length, and anchors the argument on
`\sum_{a\in S}\|b_n(a)\|_{\mathrm F}^2 = 4`.  `Sofic/CollapseWordMetric.lean`
supplies exactly those three statements for exactly that object.  The
development the endpoint travels, however, still runs on
`InvolutionCollapseProfile.bVec`, which is the printed vector *capped to zero*
at the stages before the Step-3 threshold; that is audit rows `CO.07`, `CO.09`
and `CO.09b` (`notes/COLLAPSE_STEP_AUDIT.md`, COL.17, COL.19, COL.20).

This module is the bridge that lets the endpoint state its conclusions about the
printed vector without reproving anything analytic.  Everything rests on one
observation, already recorded in `Sofic/CollapseWordMetricBridge.lean`: for each
fixed mover the guarded and the printed vector are **equal** at all large
stages.  Since every quantity the argument reads off the family is either a
limiting seminorm along the hyperfilter or a value at a single late stage,
eventual equality is all that is needed, and
`InvolutionCollapseCocycle.seqNormSq_congr_of_eventually_eq` converts it.

Contents, in the order the endpoint consumes them:

* `isBoundedSeq_printed` — the printed family is a bounded sequence, which is
  what the ultralimit machinery takes as input.  For the guarded vector this was
  bought by the cap; here it is `CollapseWordMetric.exists_norm_bVec_bound`,
  i.e. the eventual Step-3 bound plus the finitely many stages before it.
* `seqNormSq_printed_eq` — the two families have the same limiting squared
  seminorm at every mover.
* `printed_profile_le_num` — Step 5's bound for the printed vector:
  `seqNormSq (b_\cdot(\gamma)) \le 111/\kappa^2`, a constant depending on the
  Kazhdan pair alone.
* `printed_sum_seqNormSq_eq_four` — `eq:limit-mass` for the printed vector.
* `eventually_printed_bVec_eq_zero_of_orbit_fixed` — Step 6's first move for the
  printed vector: a mover whose orbit element is the witness itself has
  vanishing displacement at all large stages.

Nothing here weakens anything: each statement is the printed one, and each proof
is the corresponding statement about the guarded family together with the
eventual equality of the two.
-/

namespace GroupApproximation
namespace CollapsePrintedProfile

open Matrix InvolutionOrbitMicrostates InvolutionRankMass
open InvolutionCollapseMetric InvolutionMicrostateTools
open InvolutionCollapseProfile InvolutionCollapseCocycle
open InvolutionCollapseCenter InvolutionCollapseEndpointPrep
open Ultralimit KazhdanCornerMatrices KazhdanCompressorCorner
open scoped Matrix.Norms.L2Operator

attribute [local instance] InnerProductSpace.complexToReal

variable {Γ E : Type} [Group Γ] [Group E]
variable (B : OpAlmostRepresentation E)
variable (iota : Γ →* E)
variable (k : E)
variable (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ)
variable (S : Finset Γ)

/-! ## The printed family is a bounded sequence -/

/-- **The printed displacement vectors of a fixed mover are uniformly
bounded.**  The guarded development obtained this at every stage from its cap;
for the printed object it is the eventual Step-3 estimate together with the
fact that only finitely many stages precede the threshold, which is
`CollapseWordMetric.exists_norm_bVec_bound`.  Its conclusion is literally
`Ultralimit.IsBoundedSeq`, so no conversion is involved. -/
theorem isBoundedSeq_printed
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (γ : Γ) :
    IsBoundedSeq (fun n ↦ CollapseWordMetric.bVec B V S n γ) :=
  CollapseWordMetric.exists_norm_bVec_bound B iota k V S hgen hsymm hVinv
    hVcomm hVconv γ

/-! ## The two families have the same limit -/

/-- **The guard is invisible at the limit.**  For each fixed mover the guarded
and the printed displacement vectors agree at all large stages
(`CollapseWordMetricBridge.eventually_profile_bVec_eq`), and a limiting squared
seminorm of a bounded sequence depends only on its eventual values, so the two
limiting profiles coincide. -/
theorem seqNormSq_printed_eq
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (γ : Γ) :
    seqNormSq (fun n ↦ bVec B V S hgen hsymm n γ) =
      seqNormSq (fun n ↦ CollapseWordMetric.bVec B V S n γ) :=
  seqNormSq_congr_of_eventually_eq
    (isBoundedSeq_bVec B V S hgen hsymm hVinv hVcomm γ)
    (isBoundedSeq_printed B iota k V S hgen hsymm hVinv hVcomm hVconv γ)
    (CollapseWordMetricBridge.eventually_profile_bVec_eq B iota k V S hgen
      hsymm hVinv hVcomm hVconv γ)

/-! ## Step 5 for the printed vector -/

/-- **The printed limiting profile is bounded by the Kazhdan pair alone.**
This is `CollapseProfileBound.collapse_profile_le_num`, which runs Delorme's
Gaussian argument with the constant kept, read on the printed family: the
limiting profile is at most `111/\kappa^2`, with no dependence on `|S|`, on the
group, or on the model sequence.  It is the input `rem:collapse-finite-stage`
calls "a bound uniform in `\gamma` … with `C` depending on the Kazhdan pair
alone". -/
theorem printed_profile_le_num
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n)
    {κ : ℝ} (hpair : IsKazhdanPair.{0, 0} Γ S κ) (γ : Γ) :
    seqNormSq (fun n ↦ CollapseWordMetric.bVec B V S n γ) ≤ 111 / κ ^ 2 :=
  CollapseProfileBound.collapse_profile_le_num B iota k V S hgen hsymm
    hVinv hVcomm hVconv hmark hpair γ

/-- **The limit-level mass anchor for the printed vector.**  Equation
`eq:limit-mass`: the generators carry total limiting squared mass exactly
four. -/
theorem printed_sum_seqNormSq_eq_four
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n) :
    ∑ a ∈ S, seqNormSq (fun n ↦ CollapseWordMetric.bVec B V S n a) = 4 := by
  have hcongr : ∀ a ∈ S,
      seqNormSq (fun n ↦ CollapseWordMetric.bVec B V S n a) =
        seqNormSq (fun n ↦ bVec B V S hgen hsymm n a) :=
    fun a _ ↦
      (seqNormSq_printed_eq B iota k V S hgen hsymm hVinv hVcomm hVconv a).symm
  rw [Finset.sum_congr rfl hcongr]
  exact sum_seqNormSq_bVec_eq_four B V S hgen hsymm hVinv hVcomm hmark

/-! ## Step 6 for the printed vector -/

/-- **Movers fixing the witness have vanishing printed displacement.**  Step 6
observes that (W2) makes `v_{sas^{-1}} = k = v_1`, so the corrected involutions
at `sas^{-1}` and at `1` agree and the displacement vanishes.  In Lean the
agreement is obtained from the rigidity of commuting exact involutions at
operator distance below `2`, which gives it at all large stages; the printed
vector inherits it through the eventual equality of the two families. -/
theorem eventually_printed_bVec_eq_zero_of_orbit_fixed
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    {δa : Γ} (hfix : orbitElement iota k δa = k) :
    ∃ N, ∀ n ≥ N, CollapseWordMetric.bVec B V S n δa = 0 := by
  obtain ⟨N₁, hN₁⟩ := eventually_bVec_eq_zero_of_orbit_fixed B iota k V S hgen
    hsymm hVinv hVcomm hVconv hfix
  obtain ⟨N₂, hN₂⟩ := CollapseWordMetricBridge.eventually_profile_bVec_eq B
    iota k V S hgen hsymm hVinv hVcomm hVconv δa
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  rw [← hN₂ n ((le_max_right _ _).trans hn)]
  exact hN₁ n ((le_max_left _ _).trans hn)

end CollapsePrintedProfile
end GroupApproximation
