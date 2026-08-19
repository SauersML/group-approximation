import GroupApproximation.Sofic.CollapseWordMetric
import GroupApproximation.Sofic.InvolutionCollapseProfile

/-!
# The guarded displacement vector is the printed one, eventually

This module reconciles the two objects named in `notes/COLLAPSE_STEP_AUDIT.md`
at COL.17 and COL.19: the chosen-word length
`InvolutionCollapseProfile.wordLen` against the genuine word length
`WordMetric.wordNorm`, and the guarded vector
`InvolutionCollapseProfile.bVec` against the printed
`CollapseWordMetric.bVec` of Step 4 of the proof sketch of `\ref{thm:collapse}`
that `non_mf_groups_exist.tex` printed until commit `3a45fa60` replaced it (see
the header of `Sofic/CollapseJointCorner.lean`).

* `wordNorm_le_wordLen` — the printed invariant is at most the chosen-word
  length, so the printed COL.17 bound implies the one previously proved
  and the printed COL.20 mass bound is the sharper of the two.
* `eventually_profile_bVec_eq` — for each fixed element the guarded vector
  **equals** the printed one at all large stages.  This is the precise
  content of the audit's remark that the guard is invisible downstream:
  every consumer of the guarded vector reads it at the ultralimit, and two
  sequences that agree eventually have the same ultralimit.

Nothing here is needed by the collapse argument itself; it exists so the
guarded development and the printed development can be interchanged
without reproving anything.
-/

namespace GroupApproximation
namespace CollapseWordMetricBridge

open Matrix InvolutionOrbitMicrostates InvolutionRankMass
open InvolutionCollapseMetric InvolutionMicrostateTools
open KazhdanCornerMatrices KazhdanCompressorCorner
open scoped Matrix.Norms.L2Operator

variable {Γ E : Type} [Group Γ] [Group E]
variable (B : OpAlmostRepresentation E)
variable (iota : Γ →* E)
variable (k : E)
variable (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ)
variable (S : Finset Γ)

/-- The genuine word length is at most the length of the chosen word: the
printed invariant `|\gamma|_S` is the sharper of the two. -/
theorem wordNorm_le_wordLen
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) (γ : Γ) :
    WordMetric.wordNorm (S : Set Γ) γ ≤
      InvolutionCollapseProfile.wordLen S hgen hsymm γ := by
  obtain ⟨l, hlS, hlprod, hllen⟩ :=
    InvolutionCollapseProfile.wordLen_spec S hgen hsymm γ
  have hw : WordMetric.IsWord (S : Set Γ) l γ :=
    ⟨fun x hx ↦ Finset.mem_coe.mpr (hlS x hx), hlprod⟩
  have h := WordMetric.wordNorm_le_length hw
  rwa [hllen] at h

/-- **The guard is eventually vacuous.**  For each fixed element the
guarded displacement vector of `InvolutionCollapseProfile` agrees, at all
large stages, with the printed vector `k_n^{-1/2}(V_n(\gamma) - V_n(1))`.

Both branches are checked: past the COL.17 threshold the guard's second
conjunct holds, so either the guard is satisfied and the two vectors are
the same expression, or `k_n = 0` and both vectors are `0`. -/
theorem eventually_profile_bVec_eq
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (γ : Γ) :
    ∃ N, ∀ n ≥ N,
      InvolutionCollapseProfile.bVec B V S hgen hsymm n γ =
        CollapseWordMetric.bVec B V S n γ := by
  obtain ⟨N, hN⟩ :=
    InvolutionCollapseProfile.eventually_dV_le_wordLen_mul_kNorm
      B iota k V S hgen hsymm hVinv hVcomm hVconv γ
  refine ⟨N, fun n hn ↦ ?_⟩
  unfold InvolutionCollapseProfile.bVec CollapseWordMetric.bVec
  split_ifs with hguard
  · rfl
  · have hk : kNorm B V S n = 0 := by
      by_contra hk0
      exact hguard ⟨Nat.pos_of_ne_zero hk0, hN n hn⟩
    rw [hk]
    simp

end CollapseWordMetricBridge
end GroupApproximation
