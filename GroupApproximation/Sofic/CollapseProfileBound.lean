import GroupApproximation.Sofic.CollapseWordMetricBridge
import GroupApproximation.Sofic.InvolutionCollapseCocycle

/-!
# The limiting profile is bounded by its generator values

`non_mf_groups_exist.tex` used to prove orbit collapse through an
approximate-cocycle estimate, and Step 5 of that proof sketch read:

> the spectral gap of `(S,\kappa)` bounds the limiting profile
> `\gamma \mapsto \lim_n \|b_n(\gamma)\|_{\mathrm F}^2` **by its
> generator values** --- Delorme's argument
> at the level of limiting seminorms.

**The printed proof no longer takes that route.**  Commit `3a45fa60` moved the
collapse mechanism entirely inside the matrix corona, and the approximate-cocycle
estimate, the rank pseudometric on the orbit and the generator-mass display all
went with it; `eq:generator-mass` is not a `\label` any more.  What
`\ref{thm:collapse}` and `\ref{thm:projection-collapse}` print in
`\ref{subsec:collapse}` is a rank-normalized Hilbertization followed by
Delorme--Guichardet, which is the divergence the proof ledger records at
`CO.19`--`CO.22`.  This module therefore formalizes a route the manuscript no
longer prints; it is correct and it is kept, but no badge is owed on it.

`Kazhdan.UltralimitGaussianBoundedness.profile_bounded_of_isKazhdanPair`
proves only the existential form `∃ R, ∀ g, profile g ≤ R`, and
`InvolutionCollapseEndpoint.no_marked_model` consumes it as an opaque
`R₀` (from which `Cw = √R + 2`).  The quantitative content sits one
level down: `Delorme.bounded_of_gaussian_isPositiveDefinite` runs its
GNS argument at `t = κ ^ 2 / (32 * B)` with `B = (∑ q ∈ Q, ψ q) + 1`,
and therefore proves `ψ ≤ Real.log 2 / t = 32 * Real.log 2 * B / κ ^ 2`.
The existential discards that witness, so the manuscript's link *to the
generator values* is not, as things stand, a Lean theorem about the
collapse profile.

This module exposes the constant and closes the link.

* `gaussian_bound_of_kazhdan_le` — Delorme's Gaussian boundedness
  principle with the bound `32 * Real.log 2 * B / ε ^ 2` displayed, for
  any `B` dominating `ψ` on the Kazhdan set.  This is the GNS argument
  of `Kazhdan/DelormeFixedPoint.lean` re-run with `B` a parameter rather
  than fixed to `(∑ q ∈ Q, ψ q) + 1`, and with the witness kept.
* `gaussian_bound_by_generator_values` — the instance
  `B = (∑ q ∈ Q, ψ q) + 1`, i.e. literally "bounded by its generator
  values", with Delorme's own constant.
* `profile_le_of_kazhdan_le`, `profile_le_by_generator_values` —
  the same two statements for the ultralimit profile of a family of
  almost-cocycles.
* `collapse_profile_le_generator_values` — the manuscript's Step 5
  sentence for the collapse family `b_n`.
* `collapse_profile_le`, `collapse_profile_le_sharp` — the numerical
  consequence.  Feeding in the limit-level anchor
  `InvolutionCollapseCocycle.sum_seqNormSq_bVec_eq_four`
  (eq. `generator-mass` at the limit: the generators carry total
  limiting mass exactly four; proved in the repository and, before this
  module, used nowhere) turns the generator-value bound into the
  absolute constant `160 * Real.log 2 / κ ^ 2`, and the sharper choice
  `B = 4` into `128 * Real.log 2 / κ ^ 2`.  Neither depends on `|S|`, on
  the group, or on the model sequence: only on the Kazhdan constant.

The numerical corollaries (`≤ 111 / κ ^ 2`, and the resulting bound on
`Cw`) are in `Sofic/CollapseProfileBoundNumeric.lean`, which is the only
file needing `Real.log_two_lt_d9`.
-/

namespace GroupApproximation
namespace CollapseProfileBound

universe u v

/-! ## Delorme's Gaussian boundedness principle, with the constant kept -/

section Abstract

open KazhdanGNS KazhdanFixedSpace

variable {G : Type u} [Group G]

/-- **Gaussian boundedness with an explicit constant.**  On a group with
a Kazhdan pair `(Q, ε)`, a nonnegative function `ψ` vanishing at the
identity all of whose Gaussians `exp (-t * ψ)` are positive-definite is
bounded *by its values on the Kazhdan set*: if `ψ q ≤ B` for every
`q ∈ Q` then `ψ ≤ 32 * log 2 * B / ε ^ 2` everywhere.

This is `Delorme.bounded_of_gaussian_isPositiveDefinite` with the
witness exposed instead of existentially quantified.  The proof is the
same one: the GNS cyclic vector of the Gaussian at `t = ε ^ 2 / (32 * B)`
is `(Q, ε)`-almost invariant, so the Kazhdan spectral gap puts its
moving component below `1 / 4` in norm, so the Gaussian is at least
`1 / 2` everywhere, so `t * ψ ≤ log 2`.  Only the last step changes: the
threshold `log 2 / t` is recorded rather than discarded.  Nonnegativity
of `ψ` is not needed once `B` is given; it is needed only to produce `B`
from the generator values, which is
`gaussian_bound_by_generator_values`. -/
theorem gaussian_bound_of_kazhdan_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (ψ : G → ℝ) (hψ1 : ψ 1 = 0)
    (hpd : ∀ t : ℝ, 0 < t →
      KazhdanFiniteModel.IsPositiveDefinite
        (fun g ↦ Real.exp (-t * ψ g)))
    {Bnd : ℝ} (hBpos : 0 < Bnd) (hBq : ∀ q ∈ Q, ψ q ≤ Bnd) (x : G) :
    ψ x ≤ 32 * Real.log 2 * Bnd / ε ^ 2 := by
  classical
  have hε := hQ.1
  set t : ℝ := ε ^ 2 / (32 * Bnd) with ht
  have htpos : 0 < t := by
    rw [ht]
    exact div_pos (pow_pos hε 2) (by linarith)
  -- The Gaussian positive-definite function and its GNS data.
  set p : PositiveDefiniteFunction G :=
    ⟨fun y ↦ Real.exp (-t * ψ y), hpd t htpos⟩ with hp
  have hpapply : ∀ y : G, p y = Real.exp (-t * ψ y) := fun y ↦ by
    rw [hp]
  set ρ := representation p with hρ
  set ξ := kernelVector p 1 with hξ
  have hξsq : inner ℝ ξ ξ = 1 := by
    rw [hξ, inner_kernelVector]
    show Real.exp (-t * ψ (1⁻¹ * 1)) = 1
    rw [inv_one, one_mul, hψ1]
    simp
  have hnormξsq : ‖ξ‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hξsq
  -- Displacement of the cyclic vector.
  have hdisp : ∀ q : G, ‖ρ q ξ - ξ‖ ^ 2 = 2 - 2 * p q := by
    intro q
    have hρξ : ρ q ξ = kernelVector p q := by
      rw [hρ, hξ, representation_kernelVector, mul_one]
    have hinner : inner ℝ ξ (kernelVector p q) = p q := by
      rw [hξ, inner_kernelVector, inv_one, one_mul]
    have hkq : ‖kernelVector p q‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, inner_kernelVector, inv_mul_cancel]
      show Real.exp (-t * ψ 1) = 1
      rw [hψ1]
      simp
    rw [norm_sub_rev, norm_sub_sq_real, hρξ, hinner, hnormξsq, hkq]
    ring
  have hdispQ : ∀ q ∈ Q, ‖ρ q ξ - ξ‖ ^ 2 ≤ 2 * t * Bnd := by
    intro q hq
    rw [hdisp q]
    have hple : 1 - t * ψ q ≤ p q := by
      rw [hpapply q]
      have hexp := Real.add_one_le_exp (-t * ψ q)
      linarith
    have htB : t * ψ q ≤ t * Bnd :=
      mul_le_mul_of_nonneg_left (hBq q hq) htpos.le
    linarith
  -- The moving component of the cyclic vector.
  set m := subgroupMovingProjection ρ ⊤ ξ with hm
  have hPfix : ∀ s : G,
      ρ s (fixedProjection ρ ⊤ ξ : HilbertSpace p) =
        (fixedProjection ρ ⊤ ξ : HilbertSpace p) :=
    fun s ↦ fixedProjection_mem ρ ⊤ ξ ⟨s, Subgroup.mem_top s⟩
  have hdecomp : ξ = (fixedProjection ρ ⊤ ξ : HilbertSpace p) + m := by
    rw [hm, subgroupMovingProjection_eq_sub_fixedProjection]
    abel
  have hsplit : ∀ q : G, ρ q m - m = ρ q ξ - ξ := by
    intro q
    conv_rhs => rw [hdecomp]
    rw [map_add, hPfix q]
    abel
  -- Kazhdan spectral gap on the moving subspace.
  have hmsq : ε ^ 2 * ‖m‖ ^ 2 ≤ 2 * t * Bnd := by
    by_cases hm0 : m = 0
    · rw [hm0, norm_zero]
      have h2tB : 0 ≤ 2 * t * Bnd :=
        mul_nonneg (mul_nonneg (by norm_num) htpos.le) hBpos.le
      nlinarith
    · have hmem : m ∈ movingSubspace ρ := by
        rw [hm]
        exact subgroupMovingProjection_mem ρ ⊤ ξ
      letI : CompleteSpace (movingSubspace ρ) :=
        (Submodule.isClosed_orthogonal _).completeSpace_coe
      set y : movingSubspace ρ := ⟨m, hmem⟩ with hy
      have hy0 : y ≠ 0 := by
        intro hc
        apply hm0
        have hval := congrArg Subtype.val hc
        simpa [hy] using hval
      obtain ⟨q, hq, hqmove⟩ :=
        IsKazhdanPair.exists_moved_mul_norm_of_noInvariant hQ
          (movingRepresentation ρ)
          (movingRepresentation_hasNoInvariantVectors ρ) y hy0
      have hynorm : ‖y‖ = ‖m‖ := rfl
      have hcoe : ((movingRepresentation ρ q y - y : movingSubspace ρ) :
          HilbertSpace p) = ρ q m - m := by
        simp [hy]
      have htransfer : ‖movingRepresentation ρ q y - y‖ = ‖ρ q ξ - ξ‖ := by
        rw [show ‖movingRepresentation ρ q y - y‖ =
          ‖((movingRepresentation ρ q y - y : movingSubspace ρ) :
            HilbertSpace p)‖ from rfl, hcoe, hsplit q]
      rw [hynorm, htransfer] at hqmove
      have hsq := mul_self_le_mul_self
        (mul_nonneg hε.le (norm_nonneg m)) hqmove
      have hd2 := hdispQ q hq
      nlinarith [norm_nonneg (ρ q ξ - ξ)]
  -- The moving component is below one quarter in square.
  have h2tB : 2 * t * Bnd = ε ^ 2 / 16 := by
    rw [ht]
    field_simp [hBpos.ne']
    ring
  have hm16 : ‖m‖ ^ 2 ≤ 1 / 16 := by
    rw [h2tB] at hmsq
    nlinarith [pow_pos hε 2]
  -- Uniform lower bound for the Gaussian.
  have hcross1 : ∀ y : G,
      inner ℝ (fixedProjection ρ ⊤ ξ : HilbertSpace p) (ρ y m) = 0 := by
    intro y
    apply Submodule.inner_right_of_mem_orthogonal
      (K := fixedSubspace ρ ⊤)
    · exact (fixedProjection ρ ⊤ ξ).property
    · apply map_mem_fixedSubspace_orthogonal_of_normal ρ ⊤ y
      rw [hm]
      exact subgroupMovingProjection_mem ρ ⊤ ξ
  have hcross2 : inner ℝ m
      (fixedProjection ρ ⊤ ξ : HilbertSpace p) = 0 := by
    rw [real_inner_comm]
    rw [hm]
    exact fixedProjection_inner_movingProjection ρ ⊤ ξ
  have hP : ‖(fixedProjection ρ ⊤ ξ : HilbertSpace p)‖ ^ 2 =
      1 - ‖m‖ ^ 2 := by
    have hpyth := norm_sq_fixedProjection_add_movingProjection ρ ⊤ ξ
    rw [hnormξsq, ← hm] at hpyth
    linarith
  have hlower : ∀ y : G, 1 - 2 * ‖m‖ ^ 2 ≤ p y := by
    intro y
    have hpgEq : p y = inner ℝ ξ (ρ y ξ) := by
      rw [hρ, hξ, representation_kernelVector, mul_one,
        inner_kernelVector, inv_one, one_mul]
    have hexpand : inner ℝ ξ (ρ y ξ) =
        ‖(fixedProjection ρ ⊤ ξ : HilbertSpace p)‖ ^ 2 +
          inner ℝ m (ρ y m) := by
      conv_lhs => rw [hdecomp]
      rw [map_add, hPfix y, inner_add_left, inner_add_right,
        inner_add_right, hcross1 y, hcross2,
        real_inner_self_eq_norm_sq]
      ring
    rw [hpgEq, hexpand, hP]
    have hcs := abs_real_inner_le_norm m (ρ y m)
    rw [(ρ y).norm_map] at hcs
    have hneg := neg_abs_le (inner ℝ m (ρ y m))
    nlinarith
  -- Invert the exponential, keeping the threshold.
  have hpg : (1 : ℝ) / 2 ≤ Real.exp (-t * ψ x) := by
    have hlow := hlower x
    rw [hpapply x] at hlow
    linarith [hm16]
  have h12 : Real.exp (Real.log (1 / 2)) ≤ Real.exp (-t * ψ x) := by
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
    exact hpg
  have hlog := Real.exp_le_exp.mp h12
  rw [show Real.log (1 / 2 : ℝ) = -Real.log 2 from by
    rw [one_div, Real.log_inv]] at hlog
  -- `hlog : -Real.log 2 ≤ -t * ψ x`; clear the denominators.
  have htψ : t * ψ x ≤ Real.log 2 := by nlinarith [hlog]
  have h32B : (0 : ℝ) < 32 * Bnd := by linarith
  have h32Bne : (32 : ℝ) * Bnd ≠ 0 := ne_of_gt h32B
  have htcancel : t * (32 * Bnd) = ε ^ 2 := by
    rw [ht]
    exact div_mul_cancel₀ _ h32Bne
  have hexpand : t * ψ x * (32 * Bnd) = ψ x * ε ^ 2 := by
    calc
      t * ψ x * (32 * Bnd) = t * (32 * Bnd) * ψ x := by ring
      _ = ε ^ 2 * ψ x := by rw [htcancel]
      _ = ψ x * ε ^ 2 := by ring
  have hkey := mul_le_mul_of_nonneg_right htψ h32B.le
  rw [hexpand, show Real.log 2 * (32 * Bnd) = 32 * Real.log 2 * Bnd from
    by ring] at hkey
  rw [le_div_iff₀ (pow_pos hε 2)]
  exact hkey

/-- **Bounded by its generator values.**  The instance
`B = (∑ q ∈ Q, ψ q) + 1` of `gaussian_bound_of_kazhdan_le`: the bound on
`ψ` over the whole group is the explicit function
`32 * log 2 * ((∑ q ∈ Q, ψ q) + 1) / ε ^ 2` of the values of `ψ` on the
Kazhdan set.  This is exactly the constant that
`Delorme.bounded_of_gaussian_isPositiveDefinite` produces internally and
then hides behind an existential. -/
theorem gaussian_bound_by_generator_values
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (ψ : G → ℝ) (hψ1 : ψ 1 = 0) (hψnn : ∀ g : G, 0 ≤ ψ g)
    (hpd : ∀ t : ℝ, 0 < t →
      KazhdanFiniteModel.IsPositiveDefinite
        (fun g ↦ Real.exp (-t * ψ g)))
    (x : G) :
    ψ x ≤ 32 * Real.log 2 * ((∑ q ∈ Q, ψ q) + 1) / ε ^ 2 := by
  have hsumnn : 0 ≤ ∑ q ∈ Q, ψ q :=
    Finset.sum_nonneg fun q _ ↦ hψnn q
  refine gaussian_bound_of_kazhdan_le hQ ψ hψ1 hpd (by linarith) ?_ x
  intro q hq
  have hle := Finset.single_le_sum (f := fun q ↦ ψ q)
    (fun i _ ↦ hψnn i) hq
  linarith

end Abstract

/-! ## The same two bounds for the ultralimit profile -/

section Profile

open Ultralimit UltralimitGaussian

variable {G : Type u} [Group G] {H : ℕ → Type v}
  [∀ k, NormedAddCommGroup (H k)] [∀ k, InnerProductSpace ℝ (H k)]

/-- **Scalar Delorme at the ultralimit, with the constant exposed.**  The
quantitative form of
`UltralimitGaussian.profile_bounded_of_isKazhdanPair`: if the limiting
profile of a family of almost-cocycles is at most `B` on the Kazhdan set,
then it is at most `32 * log 2 * B / κ ^ 2` everywhere.  As in the
existential version, only the limiting displacement identity `halmost`
is needed; no stage has to be a cocycle. -/
theorem profile_le_of_kazhdan_le {Q : Finset G} {κ : ℝ}
    (hQ : IsKazhdanPair.{u, u} G Q κ) {b : ∀ k, G → H k}
    (hbdd : ∀ g : G, ∃ C : ℝ, ∀ k, ‖b k g‖ ^ 2 ≤ C)
    (hone : ∀ k, b k 1 = 0)
    (halmost : ∀ g h : G,
      ArchimedeanClass.stdPart
          (Hyperreal.ofSeq fun k ↦ ‖b k (g⁻¹ * h)‖ ^ 2) =
        ArchimedeanClass.stdPart
          (Hyperreal.ofSeq fun k ↦ ‖b k h - b k g‖ ^ 2))
    {Bnd : ℝ} (hBpos : 0 < Bnd)
    (hBq : ∀ q ∈ Q, profile b q ≤ Bnd) (x : G) :
    profile b x ≤ 32 * Real.log 2 * Bnd / κ ^ 2 :=
  gaussian_bound_of_kazhdan_le hQ (profile b) (profile_one hone)
    (fun _t ht ↦ isPositiveDefinite_exp_neg_mul_profile hbdd halmost ht.le)
    hBpos hBq x

/-- **The limiting profile is bounded by its generator values.**  The
manuscript's Step 5 assertion, at the level of the abstract ultralimit
profile: the bound over the whole group is an explicit function of the
Kazhdan constant and of the profile's values on the Kazhdan set. -/
theorem profile_le_by_generator_values {Q : Finset G} {κ : ℝ}
    (hQ : IsKazhdanPair.{u, u} G Q κ) {b : ∀ k, G → H k}
    (hbdd : ∀ g : G, ∃ C : ℝ, ∀ k, ‖b k g‖ ^ 2 ≤ C)
    (hone : ∀ k, b k 1 = 0)
    (halmost : ∀ g h : G,
      ArchimedeanClass.stdPart
          (Hyperreal.ofSeq fun k ↦ ‖b k (g⁻¹ * h)‖ ^ 2) =
        ArchimedeanClass.stdPart
          (Hyperreal.ofSeq fun k ↦ ‖b k h - b k g‖ ^ 2))
    (x : G) :
    profile b x ≤
      32 * Real.log 2 * ((∑ q ∈ Q, profile b q) + 1) / κ ^ 2 :=
  gaussian_bound_by_generator_values hQ (profile b) (profile_one hone)
    (fun g ↦ profile_nonneg hbdd g)
    (fun _t ht ↦ isPositiveDefinite_exp_neg_mul_profile hbdd halmost ht.le)
    x

end Profile

/-! ## The collapse family: the generator values are known exactly -/

section Collapse

open Matrix InvolutionOrbitMicrostates InvolutionRankMass
open InvolutionCollapseMetric InvolutionMicrostateTools
open InvolutionCollapseProfile InvolutionCollapseCocycle
open Ultralimit UltralimitGaussian KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

attribute [local instance] InnerProductSpace.complexToReal

variable {Γ E : Type} [Group Γ] [Group E]
variable (B : OpAlmostRepresentation E)
variable (iota : Γ →* E)
variable (k : E)
variable (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ)
variable (S : Finset Γ)

/-- Stagewise squared norms of the collapse displacement vectors are
uniformly bounded, elementwise: the `hbdd` input of the ultralimit
Gaussian machinery. -/
theorem bVec_normSq_bdd (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁) :
    ∀ g : Γ, ∃ C : ℝ, ∀ n, ‖bVec B V S hgen hsymm n g‖ ^ 2 ≤ C :=
  fun g ↦ ⟨4 * (wordLen S hgen hsymm g : ℝ),
    fun n ↦ norm_bVec_sq_le B V S hgen hsymm hVinv hVcomm n g⟩

/-- **Step 5, "bounds the limiting profile by its generator values".**
The Kazhdan pair `(S, κ)` bounds the limiting profile
`γ ↦ seqNormSq (b · γ)` of the collapse family by an explicit function
of `κ` and of the profile's values on `S` --- Delorme's argument at the
level of limiting seminorms, with the constant displayed rather than
existentially quantified. -/
theorem collapse_profile_le_generator_values
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n)
    {κ : ℝ} (hpair : IsKazhdanPair.{0, 0} Γ S κ) (γ : Γ) :
    seqNormSq (fun n ↦ bVec B V S hgen hsymm n γ) ≤
      32 * Real.log 2 *
          ((∑ a ∈ S, seqNormSq (fun n ↦ bVec B V S hgen hsymm n a)) + 1) /
        κ ^ 2 :=
  profile_le_by_generator_values
    (b := fun n (γ' : Γ) ↦ bVec B V S hgen hsymm n γ') hpair
    (bVec_normSq_bdd B V S hgen hsymm hVinv hVcomm)
    (fun n ↦ bVec_one B V S hgen hsymm n)
    (profile_halmost B iota k V S hgen hsymm hVinv hVcomm hVconv hmark) γ

/-- **The explicit collapse profile bound.**  Substituting the limit
level anchor `sum_seqNormSq_bVec_eq_four` (eq. `generator-mass`: the
generators carry total limiting mass exactly four) into
`collapse_profile_le_generator_values` turns the generator-value bound
into an absolute constant: the limiting profile of the collapse family
is at most `160 * log 2 / κ ^ 2` --- a bound depending on nothing but
the Kazhdan constant of `(S, κ)`.  In particular it is independent of
`|S|`, of the group, and of the model sequence. -/
theorem collapse_profile_le_of_data
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n)
    {κ : ℝ} (hpair : IsKazhdanPair.{0, 0} Γ S κ) (γ : Γ) :
    seqNormSq (fun n ↦ bVec B V S hgen hsymm n γ) ≤
      160 * Real.log 2 / κ ^ 2 := by
  have hanchor := sum_seqNormSq_bVec_eq_four B V S hgen hsymm hVinv
    hVcomm hmark
  have hgv := collapse_profile_le_generator_values B iota k V S hgen
    hsymm hVinv hVcomm hVconv hmark hpair γ
  rw [hanchor] at hgv
  rw [show (32 : ℝ) * Real.log 2 * (4 + 1) = 160 * Real.log 2 from
    by ring] at hgv
  exact hgv

/-- **The explicit collapse profile bound, with every input bound after the
colon.**  This is the declaration the manuscript badges at
`eq:profile-explicit`, and the reason it is stated this way rather than over
section variables is that a badge on a declaration carrying leading binders
certifies a *parameterized* statement, not the printed one; the zero-input gate
`check_non_mf_zero_input` enforces exactly that.  The mathematics is
`collapse_profile_le_of_data`, which is this theorem with the data in leading
position.

The bound is `160 log 2 / κ²`, the first inequality of `eq:profile-explicit`.

The displacement vector is the **printed** one, `CollapseWordMetric.bVec`: the
`b(γ)` of `eq:profile-explicit` is the limiting cocycle of the printed `b_n`,
and the badge should name what the manuscript displays.  Nothing is lost
crossing over — the capped and printed families agree at all large stages for
each fixed mover, so their limiting seminorms are equal — but the crossing is
made here rather than left as an inference for the reader. -/
theorem collapse_profile_le :
    ∀ {Γ E : Type} [Group Γ] [Group E]
      (B : OpAlmostRepresentation E) (iota : Γ →* E) (k : E)
      (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ) (S : Finset Γ)
      (_hgen : Subgroup.closure (S : Set Γ) = ⊤)
      (_hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
      (_hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
      (_hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
      (_hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
      (_hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n)
      {κ : ℝ} (_hpair : IsKazhdanPair.{0, 0} Γ S κ) (γ : Γ),
      seqNormSq (fun n ↦ CollapseWordMetric.bVec B V S n γ) ≤
        160 * Real.log 2 / κ ^ 2 := by
  intro Γ E _ _ B iota k V S hgen hsymm hVinv hVcomm hVconv hmark κ hpair γ
  have hcap : IsBoundedSeq (fun n ↦ bVec B V S hgen hsymm n γ) := by
    refine ⟨Real.sqrt (4 * (wordLen S hgen hsymm γ : ℝ)), fun n ↦ ?_⟩
    have hsq := norm_bVec_sq_le B V S hgen hsymm hVinv hVcomm n γ
    have hnn := norm_nonneg (bVec B V S hgen hsymm n γ)
    nlinarith [Real.sq_sqrt (by positivity :
        (0 : ℝ) ≤ 4 * (wordLen S hgen hsymm γ : ℝ)),
      Real.sqrt_nonneg (4 * (wordLen S hgen hsymm γ : ℝ))]
  have hprn : IsBoundedSeq (fun n ↦ CollapseWordMetric.bVec B V S n γ) :=
    CollapseWordMetric.exists_norm_bVec_bound B iota k V S hgen hsymm hVinv
      hVcomm hVconv γ
  rw [← seqNormSq_congr_of_eventually_eq hcap hprn
    (CollapseWordMetricBridge.eventually_profile_bVec_eq B iota k V S hgen
      hsymm hVinv hVcomm hVconv γ)]
  exact collapse_profile_le_of_data B iota k V S hgen hsymm hVinv hVcomm
    hVconv hmark hpair γ

/-- The sharper instance of the same threading.  Each individual
generator value is at most the total limiting mass `4`, so
`gaussian_bound_of_kazhdan_le` may be applied at `B = 4` rather than at
Delorme's `B = (∑ q ∈ S, ψ q) + 1 = 5`, improving the constant from
`160 * log 2` to `128 * log 2`. -/
theorem collapse_profile_le_sharp
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n)
    {κ : ℝ} (hpair : IsKazhdanPair.{0, 0} Γ S κ) (γ : Γ) :
    seqNormSq (fun n ↦ bVec B V S hgen hsymm n γ) ≤
      128 * Real.log 2 / κ ^ 2 := by
  have hbdd := bVec_normSq_bdd B V S hgen hsymm hVinv hVcomm
  have hanchor := sum_seqNormSq_bVec_eq_four B V S hgen hsymm hVinv
    hVcomm hmark
  have hnn : ∀ a ∈ S,
      0 ≤ seqNormSq (fun n ↦ bVec B V S hgen hsymm n a) :=
    fun a _ ↦
      profile_nonneg (b := fun n (γ' : Γ) ↦ bVec B V S hgen hsymm n γ')
        hbdd a
  have hBq : ∀ q ∈ S,
      profile (fun n (γ' : Γ) ↦ bVec B V S hgen hsymm n γ') q ≤ 4 := by
    intro q hq
    have hle := Finset.single_le_sum
      (f := fun a ↦ seqNormSq (fun n ↦ bVec B V S hgen hsymm n a))
      hnn hq
    rw [hanchor] at hle
    exact hle
  have hmain := profile_le_of_kazhdan_le
    (b := fun n (γ' : Γ) ↦ bVec B V S hgen hsymm n γ') hpair hbdd
    (fun n ↦ bVec_one B V S hgen hsymm n)
    (profile_halmost B iota k V S hgen hsymm hVinv hVcomm hVconv hmark)
    (by norm_num : (0 : ℝ) < 4) hBq γ
  rw [show (32 : ℝ) * Real.log 2 * 4 = 128 * Real.log 2 from by ring]
    at hmain
  exact hmain

end Collapse

end CollapseProfileBound
end GroupApproximation
