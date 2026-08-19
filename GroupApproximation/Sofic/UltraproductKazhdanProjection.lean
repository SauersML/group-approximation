import GroupApproximation.Analysis.KazhdanProjectionAbsorption

/-!
# The Kazhdan projection of an ultraproduct representation (KT.07–KT.09)

This module certifies steps KT.07, KT.08 and KT.09 of the ultraproduct proof
of `thm:kazhdan-transport` in `non_mf_groups_exist.tex`, the theorem captioned
*Kazhdan transport of Hilbert–Schmidt asymptotic commutants*.  Anchors are
given by label and paragraph title throughout, never by line number: the file
is under concurrent edit and its line numbers drift.  The two paragraphs
replayed here are

* *The Kazhdan projection*: with `h` the Hermitian part of
  `|S|⁻¹ Σ_{s' ∈ S} π(ι s')`, the spectrum satisfies
  `sp(h) ⊆ [-1, 1 - κ²/(2|S|)] ∪ {1}`, and the spectral projection `P` of
  `h` at the isolated point `1` belongs to the algebra;
* *One-sided compression and finiteness*, first half: with `V = π(s)` and
  `Q = V P V*`, the compression `s ι(Γ) s⁻¹ ⊆ ι(Γ)` gives `P ≤ Q`, in the
  algebraic form `Q P = P` and `P Q = P`.

Everything is proved in an **abstract** unital C-star algebra `B` carrying a
homomorphism `π : H →* unitary B`, so the results apply verbatim to the norm
ultraproduct `B_ω = ∏_ω B(K_n)` of the manuscript, whatever construction
produces that algebra.  Structurally this file is
`Analysis/MaximalCStarProperCompression.lean` re-abstracted away from
`MaximalGroupCStar E`; the endgame differs, since here the ambient algebra is
*finite* and the compression is pinned rather than proper.

## The constant

`AbstractSpectralGap.unitaryAverage_spectrum_le` delivers the weaker rate
`1 - ε²/(4|S|)`: it routes through `KazhdanProjection.norm_averageOperator_pow_le`,
a *norm* contraction obtained from a two-point convexity estimate, and that
estimate loses a factor of two against the manuscript's argument.  The
manuscript instead bounds the *quadratic form*: a unit vector `ξ ⊥ Fix` is
moved by at least `κ` by some generator, so
`Re⟨π(ι s')ξ, ξ⟩ = 1 - ‖π(ι s')ξ - ξ‖²/2 ≤ 1 - κ²/2` for that generator and
`≤ 1` for the others, whence `⟨hξ, ξ⟩ ≤ 1 - κ²/(2|S|)`.
`manuscript_eigenvalue_le_of_ne_one` below formalizes exactly that argument
and `unitaryAverage_spectrum_le_manuscript` transports it to the abstract
C-star spectrum, so the printed constant `κ²/(2|S|)` — not a surrogate — is
what this file proves.  Note also that the manuscript's argument never needs
`κ ≤ 1`, so that normalisation is not assumed here.
-/

namespace GroupApproximation
namespace UltraproductKazhdanProjection

open AbstractSpectralGap CStarSpectralProjection KazhdanProjectionAbsorption
open GNSEigenvector SpectralStateWitness KazhdanProjection
open scoped ComplexOrder InnerProductSpace

noncomputable section

universe u v w

/-! ### The manuscript's quadratic-form Kazhdan bound

The Hilbert-space input of KT.07, at the manuscript's constant. -/

section QuadraticGap

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **KT.15, the Cauchy--Schwarz half.**  At *every* generator the quadratic
form of an isometric representation is bounded by the squared norm: "every
other term is at most `1`" in the printed paragraph, before normalizing. -/
theorem inner_le_norm_sq (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) (x : E) :
    ⟪ρ g x, x⟫_ℝ ≤ ‖x‖ ^ 2 := by
  have h1 : ⟪ρ g x, x⟫_ℝ ≤ ‖ρ g x‖ * ‖x‖ := real_inner_le_norm _ _
  rw [(ρ g).norm_map x] at h1
  rw [pow_two]
  exact h1

/-- **KT.15, the displaced generator.**  A generator that moves `x` by at least
`ε‖x‖` loses `ε²/2` from the quadratic form: the printed
`Re⟨π(ι(s'))ξ, ξ⟩ ≤ 1 − κ²/2`, before normalizing.

The identity behind it is the expansion `‖ρ g x − x‖² = 2‖x‖² − 2⟨ρ g x, x⟫`,
which uses only that `ρ g` is an isometry. -/
theorem inner_le_of_moved (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {g : G} {x : E} {ε : ℝ}
    (hε : 0 ≤ ε) (hmove : ε * ‖x‖ ≤ ‖ρ g x - x‖) :
    ⟪ρ g x, x⟫_ℝ ≤ (1 - ε ^ 2 / 2) * ‖x‖ ^ 2 := by
  have hnn : (0 : ℝ) ≤ ε * ‖x‖ := mul_nonneg hε (norm_nonneg x)
  have hsq2 : (ε * ‖x‖) * (ε * ‖x‖) ≤ ‖ρ g x - x‖ * ‖ρ g x - x‖ :=
    mul_self_le_mul_self hnn hmove
  have hsq : ‖ρ g x - x‖ * ‖ρ g x - x‖
      = 2 * ‖x‖ ^ 2 - 2 * ⟪ρ g x, x⟫_ℝ := by
    rw [← pow_two, norm_sub_sq_real, (ρ g).norm_map x]
    ring
  have hexp : (ε * ‖x‖) * (ε * ‖x‖) = ε ^ 2 * ‖x‖ ^ 2 := by ring
  rw [hexp, hsq] at hsq2
  nlinarith [hsq2]

/-- **KT.16, averaging the quadratic form.**  One generator losing `ε²/2` and
the rest losing nothing gives `⟨hξ, ξ⟩ ≤ (1 − ε²/(2|S|))‖ξ‖²`, which is the
last line of the printed paragraph. -/
theorem inner_averageOperator_le_of_moved (S : Finset G) (hone : (1 : G) ∈ S)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {g : G} (hgS : g ∈ S) {x : E} {ε : ℝ}
    (hε : 0 ≤ ε) (hmove : ε * ‖x‖ ≤ ‖ρ g x - x‖) :
    ⟪averageOperator S ρ x, x⟫_ℝ
      ≤ (1 - ε ^ 2 / (2 * S.card)) * ‖x‖ ^ 2 := by
  classical
  have hcardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hne : ((S.card : ℝ)) ≠ 0 := ne_of_gt hcard
  have hdefect : ∀ g' ∈ S, 0 ≤ ‖x‖ ^ 2 - ⟪ρ g' x, x⟫_ℝ :=
    fun g' _ ↦ sub_nonneg.mpr (inner_le_norm_sq ρ g' x)
  have hqdefect : ε ^ 2 / 2 * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 - ⟪ρ g x, x⟫_ℝ := by
    have := inner_le_of_moved ρ hε hmove
    nlinarith [this]
  have hsum_le : ∑ g' ∈ S, ⟪ρ g' x, x⟫_ℝ
      ≤ (S.card : ℝ) * ‖x‖ ^ 2 - ε ^ 2 / 2 * ‖x‖ ^ 2 := by
    have hsingle : ‖x‖ ^ 2 - ⟪ρ g x, x⟫_ℝ
        ≤ ∑ g' ∈ S, (‖x‖ ^ 2 - ⟪ρ g' x, x⟫_ℝ) :=
      Finset.single_le_sum hdefect hgS
    have hsum_eq : ∑ g' ∈ S, (‖x‖ ^ 2 - ⟪ρ g' x, x⟫_ℝ)
        = (S.card : ℝ) * ‖x‖ ^ 2 - ∑ g' ∈ S, ⟪ρ g' x, x⟫_ℝ := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith
  have hinner : ⟪averageOperator S ρ x, x⟫_ℝ
      = ((S.card : ℝ))⁻¹ * ∑ g' ∈ S, ⟪ρ g' x, x⟫_ℝ := by
    rw [averageOperator_apply, IsKazhdanPair.orbitAverage,
      real_inner_smul_left, sum_inner]
  have key : (S.card : ℝ) * ⟪averageOperator S ρ x, x⟫_ℝ
      ≤ (S.card : ℝ) * ‖x‖ ^ 2 - ε ^ 2 / 2 * ‖x‖ ^ 2 := by
    rw [hinner, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    exact hsum_le
  have hexp : (S.card : ℝ) * ((1 - ε ^ 2 / (2 * (S.card : ℝ))) * ‖x‖ ^ 2)
      = (S.card : ℝ) * ‖x‖ ^ 2 - ε ^ 2 / 2 * ‖x‖ ^ 2 := by
    field_simp
  exact le_of_mul_le_mul_left (by rw [hexp]; exact key) hcard

/-- **The manuscript's Kazhdan eigenvalue bound** (paragraph *The Kazhdan
projection*).  An eigenvalue of the orbit average other than `1` is at most
`1 - ε²/(2|S|)`.

The proof is the printed one.  First, the invariant part of the eigenvector
vanishes: the average fixes the invariant component and preserves its
orthocomplement, so an eigenvector for `μ ≠ 1` is orthogonal to the invariant
subspace ("Both `Fix` and its orthocomplement are invariant under each
`π(ι s')`, hence under `h`.  On `Fix`, `h = 1`").  Second, the Kazhdan pair
moves that eigenvector by at least `ε` at some generator, which turns into
`⟨ρ q x, x⟩ ≤ (1 - ε²/2)‖x‖²` by expanding `‖ρ q x - x‖²`, while
Cauchy–Schwarz gives `⟨ρ g x, x⟩ ≤ ‖x‖²` at every other generator.  Averaging
the quadratic form is the last line of the printed paragraph. -/
theorem manuscript_eigenvalue_le_of_ne_one [CompleteSpace E]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {x : E} (hx : x ≠ 0) {μ : ℝ} (hμ1 : μ ≠ 1)
    (heig : averageOperator S ρ x = μ • x) :
    μ ≤ 1 - ε ^ 2 / (2 * S.card) := by
  classical
  -- the eigenvector has no invariant component
  set U := KazhdanOrthogonal.invariantSubmodule ρ with hU
  letI : CompleteSpace U := (isClosed_invariantSubmodule ρ).completeSpace_coe
  set p : E := U.starProjection x with hp
  set w : E := Uᗮ.starProjection x with hw
  have hpmem : p ∈ U := U.starProjection_apply_mem x
  have hwmem : w ∈ Uᗮ := Uᗮ.starProjection_apply_mem x
  have hsplit : p + w = x :=
    U.starProjection_add_starProjection_orthogonal x
  have hTp : averageOperator S ρ p = p :=
    averageOperator_apply_of_invariant S hone ρ hpmem
  have hTw : averageOperator S ρ w ∈ Uᗮ :=
    averageOperator_mem_orthogonal S ρ hwmem
  have hproj : U.starProjection (averageOperator S ρ x) = p := by
    have hTx : averageOperator S ρ x = p + averageOperator S ρ w := by
      conv_lhs => rw [← hsplit]
      rw [map_add, hTp]
    rw [hTx, map_add]
    have h1 : U.starProjection p = p :=
      Submodule.starProjection_eq_self_iff.mpr hpmem
    have h2 : U.starProjection (averageOperator S ρ w) = 0 := by
      apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
        (Submodule.zero_mem U)
      intro z hz
      rw [sub_zero]
      exact (Submodule.mem_orthogonal' U _).mp hTw z hz
    rw [h1, h2, add_zero]
  have h3 := hproj
  rw [heig, map_smul, ← hp] at h3
  have h4 : (1 - μ) • p = 0 := by
    rw [sub_smul, one_smul, h3, sub_self]
  have h5 : (1 - μ) ≠ 0 := sub_ne_zero_of_ne (Ne.symm hμ1)
  have hp0 : p = 0 := (smul_eq_zero.mp h4).resolve_left h5
  have hxmem : x ∈ Uᗮ := by
    rw [← hsplit, hp0, zero_add]
    exact hwmem
  -- some generator moves it by at least `ε`
  obtain ⟨q, hqQ, hmove⟩ :=
    KazhdanOrthogonal.exists_moved_mul_norm_of_mem_orthogonal hQ ρ hxmem hx
  have hqS : q ∈ S := hQS hqQ
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hcardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hne : ((S.card : ℝ)) ≠ 0 := ne_of_gt hcard
  -- the averaged quadratic form, from KT.15 and KT.16
  have havg := inner_averageOperator_le_of_moved S hone ρ hqS hQ.1.le hmove
  have heigval : ⟪averageOperator S ρ x, x⟫_ℝ = μ * ‖x‖ ^ 2 := by
    rw [heig, real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [heigval] at havg
  have hmu : μ ≤ 1 - ε ^ 2 / (2 * (S.card : ℝ)) :=
    le_of_mul_le_mul_right (by linarith [havg]) (pow_pos hxnorm 2)
  simpa using hmu

end QuadraticGap

/-! ### The abstract spectral gap at the manuscript's rate

The C-star transport of the previous bound: the chain is the one of
`AbstractSpectralGap.unitaryAverage_spectrum_le` (a spectral value yields a
state annihilating `(m - μ)²`, GNS turns it into an eigenvector, unitaries
act isometrically and realify), with the sharper eigenvalue bound at the end.
-/

section AbstractGap

variable {G : Type u} [Group G]
variable {A : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonnegSpectrumClass ℝ A]

/-- **The abstract spectral gap at the printed rate.**  Every real spectral
value of the unitary average of a Kazhdan representation, other than `1`, is
at most `1 - ε²/(2|S|)`. -/
theorem unitaryAverage_spectrum_le_manuscript
    (ρ : G →* unitary A) {Q : Finset G} {ε : ℝ}
    (hQ : IsKazhdanPair.{u, v} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    {μ : ℝ} (hμ : (μ : ℂ) ∈ spectrum ℂ (unitaryAverage ρ S))
    (hμ1 : μ ≠ 1) :
    μ ≤ 1 - ε ^ 2 / (2 * S.card) := by
  classical
  set m : A := unitaryAverage ρ S with hm
  have hsa : IsSelfAdjoint m := isSelfAdjoint_unitaryAverage ρ hsymm
  obtain ⟨Φ, hΦ1, hΦkill⟩ := exists_state_annihilating m hsa hμ
  set ξ : Φ.GNS := gnsCyclic Φ with hξ
  have hξnorm : ‖ξ‖ = 1 := norm_gnsCyclic Φ hΦ1
  have hξne : ξ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hξnorm
    exact one_ne_zero hξnorm.symm
  have heigC : Φ.gnsStarAlgHom m ξ = (μ : ℂ) • ξ :=
    gns_eigenvector Φ m hsa μ hΦkill
  letI : InnerProductSpace ℝ Φ.GNS := InnerProductSpace.rclikeToReal ℂ Φ.GNS
  set ρU : G →* unitary (Φ.GNS →L[ℂ] Φ.GNS) :=
    (unitaryMap Φ.gnsStarAlgHom).comp ρ with hρU
  set σ : G →* (Φ.GNS ≃ₗᵢ[ℝ] Φ.GNS) :=
    (realifyIsometryHom).comp ((unitaryIsometryHom).comp ρU) with hσ
  have hsmulR : ∀ (r : ℝ) (v : Φ.GNS), (r : ℂ) • v = r • v := fun r v => by
    rw [show ((r : ℂ)) = algebraMap ℝ ℂ r by simp, algebraMap_smul]
  have havg : KazhdanProjection.averageOperator S σ ξ = μ • ξ := by
    rw [KazhdanProjection.averageOperator_apply]
    show ((S.card : ℝ))⁻¹ • ∑ g ∈ S, σ g ξ = μ • ξ
    have hterm : ∀ g ∈ S,
        σ g ξ = Φ.gnsStarAlgHom ((ρ g : unitary A) : A) ξ :=
      fun g _ => rfl
    rw [Finset.sum_congr rfl hterm]
    have hπm : Φ.gnsStarAlgHom m ξ
        = ((S.card : ℂ))⁻¹ •
          ∑ g ∈ S, Φ.gnsStarAlgHom ((ρ g : unitary A) : A) ξ := by
      rw [hm]
      show Φ.gnsStarAlgHom
          (((S.card : ℂ))⁻¹ • ∑ g ∈ S, ((ρ g : unitary A) : A)) ξ = _
      rw [map_smul, map_sum, smul_apply, sum_apply]
    calc ((S.card : ℝ))⁻¹ •
          ∑ g ∈ S, Φ.gnsStarAlgHom ((ρ g : unitary A) : A) ξ
        = ((((S.card : ℝ))⁻¹ : ℝ) : ℂ) •
          ∑ g ∈ S, Φ.gnsStarAlgHom ((ρ g : unitary A) : A) ξ :=
          (hsmulR _ _).symm
      _ = ((S.card : ℂ))⁻¹ •
          ∑ g ∈ S, Φ.gnsStarAlgHom ((ρ g : unitary A) : A) ξ := by
          congr 1
          push_cast
          ring
      _ = Φ.gnsStarAlgHom m ξ := hπm.symm
      _ = (μ : ℂ) • ξ := heigC
      _ = μ • ξ := hsmulR μ ξ
  exact manuscript_eigenvalue_le_of_ne_one hQ S hQS hone σ hξne hμ1 havg

end AbstractGap

/-! ### Unitary bookkeeping

Multiplicativity of a unitary representation read inside the algebra, and the
trivial norm bound giving the left endpoint `-1` of the printed spectral
inclusion. -/

section Unitaries

variable {G : Type u} [Group G] {A : Type v} [CStarAlgebra A]

/-- A homomorphism into the unitaries multiplies inside the algebra. -/
theorem unitary_coe_mul (ρ : G →* unitary A) (a b : G) :
    ((ρ a : unitary A) : A) * ((ρ b : unitary A) : A)
      = ((ρ (a * b) : unitary A) : A) := by
  rw [map_mul, Submonoid.coe_mul]

/-- The unitary average of a nonempty finite set has norm at most one. -/
theorem norm_unitaryAverage_le_one [Nontrivial A] (ρ : G →* unitary A)
    {S : Finset G} (hS : S.Nonempty) :
    ‖unitaryAverage ρ S‖ ≤ 1 := by
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  unfold unitaryAverage
  calc ‖((S.card : ℂ))⁻¹ • ∑ g ∈ S, ((ρ g : unitary A) : A)‖
      = ‖((S.card : ℂ))⁻¹‖ * ‖∑ g ∈ S, ((ρ g : unitary A) : A)‖ :=
        norm_smul _ _
    _ ≤ ‖((S.card : ℂ))⁻¹‖ * ∑ g ∈ S, ‖((ρ g : unitary A) : A)‖ := by
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ((S.card : ℝ))⁻¹ * S.card := by
        rw [norm_inv]
        congr 1
        · congr 1
          exact Complex.norm_natCast _
        · rw [Finset.sum_congr rfl fun g _ => CStarRing.norm_coe_unitary (ρ g)]
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hcard)

end Unitaries

/-! ### KT.07–KT.09 in an abstract unital C-star algebra -/

/-- The data of the manuscript's Kazhdan transport step, inside an abstract
unital C-star algebra `B`.

Every field is either part of the statement of `thm:kazhdan-transport`
(`pi`, `iota`, `s`, `compresses`) or the content of property `(T)` as the
manuscript itself invokes it, "*Property (T) provides a finite
symmetric generating set `S ⊆ Γ` with `1 ∈ S` and a Kazhdan constant
`κ ∈ (0,1]`*": the Kazhdan pair together with the symmetric generating
superset.  `KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair`
produces exactly `Q`, `S`, `kappa`, `kazhdan`, `QS`, `one_mem`, `symm` and
`generates` from `HasKazhdanPropertyT`; nothing here stands in for an
unformalized theorem. -/
structure KazhdanCompressionRep (Γ : Type u) (H : Type w) (B : Type v)
    [Group Γ] [Group H] [CStarAlgebra B] where
  /-- The unitary representation of the ambient group: the manuscript's `π`. -/
  pi : H →* unitary B
  /-- The Kazhdan source mapped into the ambient group. -/
  iota : Γ →* H
  /-- The compressing element. -/
  s : H
  /-- The Kazhdan set. -/
  Q : Finset Γ
  /-- The Kazhdan constant. -/
  kappa : ℝ
  /-- The Kazhdan pair, at the universe of the ambient algebra. -/
  kazhdan : IsKazhdanPair.{u, v} Γ Q kappa
  /-- The finite symmetric generating set averaged over. -/
  S : Finset Γ
  /-- The Kazhdan set sits inside the averaging set. -/
  QS : Q ⊆ S
  /-- The identity belongs to the averaging set. -/
  one_mem : 1 ∈ S
  /-- The averaging set is symmetric. -/
  symm : ∀ γ ∈ S, γ⁻¹ ∈ S
  /-- The averaging set generates the source. -/
  generates : Subgroup.closure (S : Set Γ) = ⊤
  /-- The compression hypothesis `s ι(Γ) s⁻¹ ⊆ ι(Γ)`. -/
  compresses : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ

namespace KazhdanCompressionRep

variable {Γ : Type u} {H : Type w} {B : Type v}
variable [Group Γ] [Group H] [CStarAlgebra B]
variable (D : KazhdanCompressionRep Γ H B)

/-!
The spectral order is introduced with `letI` inside the two proofs that need
it — the gap and the second-moment absorption — rather than as a file-level
instance: no statement below mentions an order on `B`, and a section-wide
`PartialOrder B` for every C-star algebra would collide with `ComplexOrder`
on `ℂ`.  This is the idiom of `CStarAlgebra.exists_sum_four_unitary` in
Mathlib. -/

/-- The averaging element `|S|⁻¹ Σ_{s' ∈ S} π(ι s')`. -/
def avg : B := unitaryAverage (D.pi.comp D.iota) D.S

/-- The manuscript's spectral rate `1 - κ²/(2|S|)`. -/
def rate : ℝ := 1 - D.kappa ^ 2 / (2 * D.S.card)

/-- The Kazhdan projection: the spectral projection of the average at the
isolated spectral point `1`. -/
def proj : B := spectralProjection (avg D) (rate D)

/-- The compressing unitary `V = π(s)`. -/
def shift : B := ((D.pi D.s : unitary B) : B)

/-- The rate is a genuine gap: `κ > 0` puts it strictly below `1`, which is
what makes `1` an isolated point of the spectrum. -/
theorem rate_lt_one : rate D < 1 := by
  have hκ : 0 < D.kappa := D.kazhdan.1
  have hcard : (0 : ℝ) < D.S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, D.one_mem⟩
  have hq : 0 < D.kappa ^ 2 / (2 * (D.S.card : ℝ)) :=
    div_pos (pow_pos hκ 2) (by linarith)
  unfold rate
  linarith

/-- The average of a symmetric set is self-adjoint: the manuscript's `h` is
the Hermitian part of the average, and here the average already equals it. -/
theorem isSelfAdjoint_avg : IsSelfAdjoint (avg D) :=
  isSelfAdjoint_unitaryAverage (D.pi.comp D.iota) D.symm

/-- The manuscript takes `h` to be the *Hermitian part* of the average.
Symmetry of `S` makes the average self-adjoint, so the Hermitian part is the
average itself and `avg` is the manuscript's `h` on the nose. -/
theorem hermitianPart_avg : (2 : ℂ)⁻¹ • (avg D + star (avg D)) = avg D := by
  rw [(isSelfAdjoint_avg D).star_eq]
  have h2 : avg D + avg D = (2 : ℂ) • avg D := (two_smul ℂ (avg D)).symm
  rw [h2, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

/-- **KT.07** (paragraph *The Kazhdan projection*).  The spectral gap of the
averaged image at the manuscript's rate: every real spectral value of `h`
other than `1` is at most `1 - κ²/(2|S|)`. -/
theorem kt_07_kazhdan_gap :
    ∀ μ ∈ spectrum ℝ (avg D), μ ≤ rate D ∨ μ = 1 := by
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  intro μ hμ
  by_cases hμ1 : μ = 1
  · exact Or.inr hμ1
  · left
    have hμℂ : (μ : ℂ) ∈ spectrum ℂ (avg D) := by
      have h := spectrum.algebraMap_mem ℂ hμ
      rwa [show (algebraMap ℝ ℂ) μ = (μ : ℂ) by simp] at h
    exact unitaryAverage_spectrum_le_manuscript (D.pi.comp D.iota) D.kazhdan
      D.S D.QS D.one_mem D.symm hμℂ hμ1

/-- The left endpoint of the printed spectral inclusion: the average of
unitaries has norm at most one, so its spectrum lies above `-1`. -/
theorem neg_one_le_of_mem_spectrum {μ : ℝ} (hμ : μ ∈ spectrum ℝ (avg D)) :
    -1 ≤ μ := by
  rcases subsingleton_or_nontrivial B with hsub | hnt
  · haveI := hsub
    exact absurd (isUnit_of_subsingleton (algebraMap ℝ B μ - avg D))
      (spectrum.mem_iff.mp hμ)
  · haveI := hnt
    have hμℂ : (μ : ℂ) ∈ spectrum ℂ (avg D) := by
      have h := spectrum.algebraMap_mem ℂ hμ
      rwa [show (algebraMap ℝ ℂ) μ = (μ : ℂ) by simp] at h
    have hb : ‖(μ : ℂ)‖ ≤ ‖avg D‖ := spectrum.norm_le_norm_of_mem hμℂ
    rw [Complex.norm_real, Real.norm_eq_abs] at hb
    have h1 : ‖avg D‖ ≤ 1 :=
      norm_unitaryAverage_le_one (D.pi.comp D.iota) ⟨1, D.one_mem⟩
    exact (abs_le.mp (le_trans hb h1)).1

/-- **KT.07, printed form**, the displayed inclusion of the paragraph *The
Kazhdan projection*:  `sp(h) ⊆ [-1, 1 - κ²/(2|S|)] ∪ {1}`. -/
theorem kt_07_spectrum_subset :
    spectrum ℝ (avg D) ⊆ Set.Icc (-1 : ℝ) (rate D) ∪ {1} := by
  intro μ hμ
  rw [Set.mem_union]
  rcases kt_07_kazhdan_gap D μ hμ with hle | h1
  · exact Or.inl (Set.mem_Icc.mpr ⟨neg_one_le_of_mem_spectrum D hμ, hle⟩)
  · exact Or.inr (Set.mem_singleton_iff.mpr h1)

/-- **KT.08**, self-adjointness of the Kazhdan projection. -/
theorem kt_08_isSelfAdjoint_proj : IsSelfAdjoint (proj D) :=
  isSelfAdjoint_spectralProjection (avg D)

/-- **KT.08**, idempotence of the Kazhdan projection. -/
theorem kt_08_proj_mul_proj : proj D * proj D = proj D :=
  isIdempotentElem_spectralProjection (avg D) (isSelfAdjoint_avg D)
    (rate_lt_one D) (kt_07_kazhdan_gap D)

/-- **KT.08**, left absorption `h P = P`: the projection lands in the
eigenspace of `h` at `1`. -/
theorem kt_08_avg_mul_proj : avg D * proj D = proj D :=
  mul_spectralProjection (avg D) (isSelfAdjoint_avg D) (rate_lt_one D)
    (kt_07_kazhdan_gap D)

/-- **KT.08**, right absorption `P h = P`. -/
theorem kt_08_proj_mul_avg : proj D * avg D = proj D :=
  spectralProjection_mul (avg D) (isSelfAdjoint_avg D) (rate_lt_one D)
    (kt_07_kazhdan_gap D)

/-- **KT.08**, the range identification `ran P = Fix` in algebraic form:
every image unitary `π(ι γ)`, for *every* `γ ∈ Γ`, fixes the projection.

The second-moment argument of `KazhdanProjectionAbsorption` turns two-sided
absorption by the average into `π(ι s') P = P` for each generator, and the
generating hypothesis propagates this to the whole group. -/
theorem kt_08_rep_mul_proj (γ : Γ) :
    ((D.pi (D.iota γ) : unitary B) : B) * proj D = proj D := by
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hfix := unitary_mul_eq_of_average_absorbs (D.pi.comp D.iota) D.symm
    (kt_08_isSelfAdjoint_proj D) (kt_08_proj_mul_proj D)
    (kt_08_avg_mul_proj D) (kt_08_proj_mul_avg D)
  have hγ : γ ∈ Subgroup.closure (D.S : Set Γ) := by
    rw [D.generates]
    trivial
  exact unitary_mul_eq_of_closure (D.pi.comp D.iota) hfix hγ

/-- **KT.08**, packaged: `P` is a projection of `B` absorbed by `h` on both
sides, and fixed by the image of `Γ`. -/
theorem kt_08_kazhdan_projection :
    IsSelfAdjoint (proj D) ∧ proj D * proj D = proj D ∧
      avg D * proj D = proj D ∧ proj D * avg D = proj D ∧
      ∀ γ : Γ, ((D.pi (D.iota γ) : unitary B) : B) * proj D = proj D :=
  ⟨kt_08_isSelfAdjoint_proj D, kt_08_proj_mul_proj D, kt_08_avg_mul_proj D,
    kt_08_proj_mul_avg D, kt_08_rep_mul_proj D⟩

/-! #### The other half of `ran P = Fix`: every fixed vector is in the range

The manuscript's `P` "projects onto `Fix`".  The inclusion `ran P ⊆ Fix` is
`kt_08_rep_mul_proj`, which is algebra-internal.  The reverse inclusion
`Fix ⊆ ran P` is a statement about vectors, so it is parametrised here by an
arbitrary action of `B` on an abelian group `K`, supplied unbundled so that a
caller with a concrete action on the Hilbert ultraproduct can use it whatever
form that action takes.  None of the action hypotheses encodes mathematics:
each is a defining property of a module action, discharged by `map_mul`,
`map_one`, `map_sub`, `map_zero`, `map_smul`, `map_sum` for anyone holding an
algebra homomorphism `B →ₐ[ℂ] (K →ₗ[ℂ] K)`.

The spectral gap enters through the resolvent factorisation
`1 - P = cfc (gapResolvent rate) h · (1 - h)`, which is where
`sp(h) ⊆ [-1, rate] ∪ {1}` is consumed: a vector killed by `1 - h` is killed
by `1 - P`, which is the operator form of "the spectral projection at the
isolated point `1` restricts to the identity on the `1`-eigenspace". -/

section FixedVectors

variable {K : Type*} [AddCommGroup K]

/-- The resolvent factorisation of the complement of the Kazhdan projection,
specialised to this data.  This is the engine of `Fix ⊆ ran P`. -/
theorem one_sub_proj_eq :
    (1 : B) - proj D
      = cfc (gapResolvent (rate D)) (avg D) * ((1 : B) - avg D) :=
  one_sub_spectralProjection_eq (avg D) (isSelfAdjoint_avg D) (rate_lt_one D)
    (kt_07_kazhdan_gap D)

/-- **Spectral step of `Fix ⊆ ran P`.**  A vector fixed by the averaged
element `h` is fixed by the Kazhdan projection `P`. -/
theorem act_proj_of_act_avg (act : B → K → K)
    (act_mul : ∀ a b ξ, act (a * b) ξ = act a (act b ξ))
    (act_one : ∀ ξ, act 1 ξ = ξ)
    (act_sub : ∀ a b ξ, act (a - b) ξ = act a ξ - act b ξ)
    (act_zero : ∀ a, act a (0 : K) = 0)
    {ζ : K} (hζ : act (avg D) ζ = ζ) :
    act (proj D) ζ = ζ := by
  have h0 : act ((1 : B) - avg D) ζ = 0 := by
    rw [act_sub, act_one, hζ, sub_self]
  have h1 : act ((1 : B) - proj D) ζ = 0 := by
    rw [one_sub_proj_eq D, act_mul, h0, act_zero]
  rw [act_sub, act_one] at h1
  exact (sub_eq_zero.mp h1).symm

/-- The `Module`-typed form of the previous lemma, for a caller whose action
is the scalar multiplication of a `Module B K`. -/
theorem smul_proj_of_smul_avg {N : Type*} [AddCommGroup N] [Module B N]
    {ζ : N} (hζ : avg D • ζ = ζ) : proj D • ζ = ζ :=
  act_proj_of_act_avg D (fun a ξ => a • ξ) (fun a b ξ => mul_smul a b ξ)
    (fun ξ => one_smul B ξ) (fun a b ξ => sub_smul a b ξ)
    (fun a => smul_zero a) hζ

variable [Module ℂ K]

/-- **Averaging step of `Fix ⊆ ran P`.**  A vector fixed by every generator
`π(ι s')`, `s' ∈ S`, is fixed by the average `h`.  Only the generators of `S`
are needed: this is the manuscript's "on `Fix`, `h = 1`". -/
theorem act_avg_of_act_rep (act : B → K → K)
    (act_smul : ∀ (c : ℂ) (a : B) (ξ : K), act (c • a) ξ = c • act a ξ)
    (act_sum : ∀ (t : Finset Γ) (f : Γ → B) (ξ : K),
      act (∑ γ ∈ t, f γ) ξ = ∑ γ ∈ t, act (f γ) ξ)
    {ζ : K} (hζ : ∀ γ ∈ D.S, act ((D.pi (D.iota γ) : unitary B) : B) ζ = ζ) :
    act (avg D) ζ = ζ := by
  classical
  have hcard : ((D.S.card : ℂ)) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨1, D.one_mem⟩
  have hsum : ∀ γ ∈ D.S,
      act ((((D.pi.comp D.iota) γ : unitary B) : B)) ζ = ζ := by
    intro γ hγ
    exact hζ γ hγ
  unfold avg unitaryAverage
  rw [act_smul, act_sum, Finset.sum_congr rfl hsum, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℂ D.S.card ζ, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

/-- **`Fix ⊆ ran P`.**  A vector fixed by every `π(ι γ)`, `γ ∈ Γ`, is fixed
by the Kazhdan projection.  Together with `kt_08_rep_mul_proj` this is the
manuscript's "`P` … projects onto `Fix`". -/
theorem kt_08_act_proj_of_fixed (act : B → K → K)
    (act_mul : ∀ a b ξ, act (a * b) ξ = act a (act b ξ))
    (act_one : ∀ ξ, act 1 ξ = ξ)
    (act_sub : ∀ a b ξ, act (a - b) ξ = act a ξ - act b ξ)
    (act_zero : ∀ a, act a (0 : K) = 0)
    (act_smul : ∀ (c : ℂ) (a : B) (ξ : K), act (c • a) ξ = c • act a ξ)
    (act_sum : ∀ (t : Finset Γ) (f : Γ → B) (ξ : K),
      act (∑ γ ∈ t, f γ) ξ = ∑ γ ∈ t, act (f γ) ξ)
    {ζ : K} (hζ : ∀ γ : Γ, act ((D.pi (D.iota γ) : unitary B) : B) ζ = ζ) :
    act (proj D) ζ = ζ :=
  act_proj_of_act_avg D act act_mul act_one act_sub act_zero
    (act_avg_of_act_rep D act act_smul act_sum fun γ _ => hζ γ)

end FixedVectors

/-- The adjoint of the shift is the image of the inverse: `V* = π(s⁻¹)`. -/
theorem star_shift : star (shift D) = ((D.pi D.s⁻¹ : unitary B) : B) :=
  star_unitary_coe D.pi D.s

/-- The shift is an isometry. -/
theorem shift_star_mul : star (shift D) * shift D = 1 :=
  (D.pi D.s).property.1

/-- The shift is a coisometry; with `shift_star_mul`, a unitary. -/
theorem shift_mul_star : shift D * star (shift D) = 1 :=
  (D.pi D.s).property.2

/-- Conjugation by the shift is the representation of conjugation in `H`:
`V π(ι γ) V* = π(s ι(γ) s⁻¹)`. -/
theorem shift_conj_coe (γ : Γ) :
    shift D * ((D.pi (D.iota γ) : unitary B) : B) * star (shift D)
      = ((D.pi (D.s * D.iota γ * D.s⁻¹) : unitary B) : B) := by
  unfold shift
  rw [star_unitary_coe D.pi D.s, unitary_coe_mul D.pi D.s (D.iota γ),
    unitary_coe_mul D.pi (D.s * D.iota γ) D.s⁻¹]

/-- **KT.09**, first half (paragraph *One-sided compression and
finiteness*).  Since `s ι(Γ) s⁻¹ ⊆ ι(Γ)`, every vector of `Fix` is fixed by
each `π(s ι(γ) s⁻¹)`; algebraically, the conjugated average absorbs the
projection. -/
theorem kt_09_conjugated_avg_mul_proj :
    (shift D * avg D * star (shift D)) * proj D = proj D := by
  classical
  have hcard : ((D.S.card : ℂ)) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨1, D.one_mem⟩
  have hconj : shift D * avg D * star (shift D)
      = ((D.S.card : ℂ))⁻¹ • ∑ γ ∈ D.S,
          ((D.pi (D.s * D.iota γ * D.s⁻¹) : unitary B) : B) := by
    unfold avg unitaryAverage
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun γ _ => ?_
    show shift D * ((D.pi (D.iota γ) : unitary B) : B) * star (shift D)
        = ((D.pi (D.s * D.iota γ * D.s⁻¹) : unitary B) : B)
    exact shift_conj_coe D γ
  rw [hconj, smul_mul_assoc, Finset.sum_mul]
  have hterm : ∀ γ ∈ D.S,
      ((D.pi (D.s * D.iota γ * D.s⁻¹) : unitary B) : B) * proj D = proj D := by
    intro γ _
    obtain ⟨δ, hδ⟩ := D.compresses γ
    rw [hδ]
    exact kt_08_rep_mul_proj D δ
  rw [Finset.sum_congr rfl hterm, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℂ D.S.card (proj D), smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

/-- **KT.09**, the inclusion `ran P ⊆ ran Q` in algebraic form: `Q P = P`.

The resolvent factorisation `1 - P = cfc h (avg) · (1 - avg)` converts
absorption by the conjugated *average* into absorption by the conjugated
*projection*, with no functional-calculus naturality. -/
theorem kt_09_conjugate_mul_proj :
    (shift D * proj D * star (shift D)) * proj D = proj D :=
  conjugated_projection_absorbs (isSelfAdjoint_avg D) (rate_lt_one D)
    (kt_07_kazhdan_gap D) (shift_star_mul D) (shift_mul_star D)
    (kt_09_conjugated_avg_mul_proj D)

/-- The conjugated projection `Q = V P V*` is self-adjoint. -/
theorem kt_09_isSelfAdjoint_conjugate :
    IsSelfAdjoint (shift D * proj D * star (shift D)) := by
  rw [IsSelfAdjoint, star_mul, star_mul, star_star,
    (kt_08_isSelfAdjoint_proj D).star_eq, mul_assoc]

/-- The adjoint form of the same inclusion: `P Q = P`. -/
theorem kt_09_proj_mul_conjugate :
    proj D * (shift D * proj D * star (shift D)) = proj D := by
  have h := congrArg star (kt_09_conjugate_mul_proj D)
  rw [star_mul, (kt_08_isSelfAdjoint_proj D).star_eq,
    (kt_09_isSelfAdjoint_conjugate D).star_eq] at h
  exact h

/-- **KT.09** (paragraph *One-sided compression and finiteness*).  With
`V = π(s)` and `Q = V P V*`, the one-sided compression `s ι(Γ) s⁻¹ ⊆ ι(Γ)`
gives `P ≤ Q`, spelled out as the two absorption identities `Q P = P` and
`P Q = P`.

Together with `kt_08_isSelfAdjoint_proj`, `kt_08_proj_mul_proj`,
`shift_star_mul` and `shift_mul_star` this is exactly the hypothesis list of
`ProperIsometryFromCompression.unitary_conjugate_eq_of_absorbs`, which is the
finiteness step KT.10. -/
theorem kt_09_one_sided_compression :
    (shift D * proj D * star (shift D)) * proj D = proj D ∧
      proj D * (shift D * proj D * star (shift D)) = proj D :=
  ⟨kt_09_conjugate_mul_proj D, kt_09_proj_mul_conjugate D⟩

end KazhdanCompressionRep

end

end UltraproductKazhdanProjection
end GroupApproximation
