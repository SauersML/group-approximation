import GroupApproximation.Sofic.CollapsePrintedProfile
import GroupApproximation.Sofic.CollapseTransportDiagonalization

/-!
# The diagonalized primitive, read on the printed displacement vector

`Sofic/CollapseTransportDiagonalization.lean` produces the input of the
rank-weight transport: a cofinal reindexing `φ` and a primitive `W` whose
coboundary defect against the displacement vectors is below the explicit rate
`2/(j+1)` at **every** stage `j`.  It states that over
`InvolutionCollapseProfile.bVec`, the displacement vector *capped* to zero
before the Step-3 threshold.

The endpoint no longer carries the capped vector anywhere: `no_marked_model`
runs on `CollapseWordMetric.bVec`, which is the printed
`b_n(\gamma) = k_n^{-1/2}(V_n(\gamma) - V_n(1))` of Step 4.  Feeding the
transport route with the capped diagonalization would put the capped object
back into the endpoint — closing `CO.14` by undoing `CO.09`.  This module
removes that trade.

The repair is a shift, not a reproof.  For each fixed mover the two vectors are
**equal** at all large stages (`CollapseWordMetricBridge.eventually_profile_bVec_eq`),
and the mover set `T` is finite, so a single threshold `N = T.sup` works for all
of them at once.  Reindexing `φ` by `j ↦ φ (j + N)` moves every stage past that
threshold while keeping cofinality — `j ≤ j + N ≤ φ (j + N)` — and the rate only
improves, since `2/((j+N)+1) ≤ 2/(j+1)`.
-/

namespace GroupApproximation
namespace CollapsePrintedDiagonalization

open Matrix InvolutionOrbitMicrostates InvolutionRankMass
open InvolutionCollapseMetric InvolutionMicrostateTools
open InvolutionCollapseProfile InvolutionCollapseCocycle
open InvolutionCollapseCenter InvolutionCollapseEndpointPrep
open CollapseTransportDiagonalization
open Ultralimit KazhdanCornerMatrices KazhdanCompressorCorner
open scoped Matrix.Norms.L2Operator

attribute [local instance] InnerProductSpace.complexToReal

variable {Γ E : Type} [Group Γ] [Group E]
variable (B : OpAlmostRepresentation E)
variable (iota : Γ →* E)
variable (k : E)
variable (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ)
variable (S : Finset Γ)

/-- **A single threshold past which the two displacement vectors agree on a
finite mover set.**  Each mover has its own threshold; `Finset.sup` over the
finite set makes one that serves them all. -/
theorem exists_uniform_agreement_threshold
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (T : Finset Γ) :
    ∃ N : ℕ, ∀ a ∈ T, ∀ n ≥ N,
      bVec B V S hgen hsymm n a = CollapseWordMetric.bVec B V S n a := by
  classical
  have hpt : ∀ a : Γ, ∃ N : ℕ, ∀ n ≥ N,
      bVec B V S hgen hsymm n a = CollapseWordMetric.bVec B V S n a :=
    fun a ↦ CollapseWordMetricBridge.eventually_profile_bVec_eq B iota k V S
      hgen hsymm hVinv hVcomm hVconv a
  choose Na hNa using hpt
  exact ⟨T.sup Na, fun a ha n hn ↦
    hNa a n (le_trans (Finset.le_sup (f := Na) ha) hn)⟩

/-- **The diagonalized primitive, against the printed displacement vector.**
Exactly `CollapseTransportDiagonalization.exists_cofinal_vanishing_coboundary_primitive`,
with `CollapseWordMetric.bVec` in place of the capped vector: a cofinal
reindexing `φ`, a primitive bounded by `√R + 2` at every stage, and the
coboundary defect below `2/(j+1)` at every stage and every mover of `T`.

These are the two hypotheses `CollapseScaledStepSix` needs at the rank weight,
now stated over the object Step 4 prints. -/
theorem exists_cofinal_vanishing_coboundary_primitive_printed
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n)
    {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ γ : Γ,
      seqNormSq (fun n ↦ CollapseWordMetric.bVec B V S n γ) ≤ R)
    (T : Finset Γ) :
    ∃ (φ : ℕ → ℕ)
      (W : ∀ j, EuclideanSpace ℂ (B.model (φ j) × B.model (φ j))),
      (∀ j, j ≤ φ j) ∧ (∀ j, ‖W j‖ ≤ Real.sqrt R + 2) ∧
      ∀ a ∈ T, ∀ j : ℕ,
        ‖CollapseWordMetric.bVec B V S (φ j) a -
          (W j - adFlat (B.map (φ j) (iota a) :
            Matrix (B.model (φ j)) (B.model (φ j)) ℂ) (W j))‖ ^ 2 ≤
          2 * (1 / ((j : ℝ) + 1)) := by
  classical
  -- the same profile bound for the capped family
  have hRcap : ∀ γ : Γ,
      seqNormSq (fun n ↦ bVec B V S hgen hsymm n γ) ≤ R := by
    intro γ
    rw [CollapsePrintedProfile.seqNormSq_printed_eq B iota k V S hgen hsymm
      hVinv hVcomm hVconv γ]
    exact hR γ
  obtain ⟨φ₀, W₀, hφ₀, hW₀, hdef₀⟩ :=
    exists_cofinal_vanishing_coboundary_primitive B iota k V S hgen hsymm
      hVinv hVcomm hVconv hmark hR0 hRcap T
  obtain ⟨N, hN⟩ := exists_uniform_agreement_threshold B iota k V S hgen hsymm
    hVinv hVcomm hVconv T
  refine ⟨fun j ↦ φ₀ (j + N), fun j ↦ W₀ (j + N), fun j ↦ ?_, fun j ↦ ?_,
    fun a ha j ↦ ?_⟩
  · exact le_trans (Nat.le_add_right j N) (hφ₀ (j + N))
  · exact hW₀ (j + N)
  · -- past the threshold the printed and capped vectors are the same vector
    have hthr : N ≤ φ₀ (j + N) :=
      le_trans (Nat.le_add_left N j) (hφ₀ (j + N))
    rw [← hN a ha (φ₀ (j + N)) hthr]
    refine le_trans (hdef₀ a ha (j + N)) ?_
    -- and the rate only improves
    have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hle : (j : ℝ) + 1 ≤ ((j + N : ℕ) : ℝ) + 1 := by
      push_cast
      have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have hdiv := one_div_le_one_div_of_le hjpos hle
    linarith

end CollapsePrintedDiagonalization
end GroupApproximation
