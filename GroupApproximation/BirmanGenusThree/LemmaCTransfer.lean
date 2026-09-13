import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Group.Torsion

/-!
# Lemma C, algebraic core: a split cyclic factor cannot see a central element

Lemma C of the genus-3 argument (research/artifacts/bh-birman-genus3-section-2026-09-12.md §3, with the details in
research/artifacts/fz-birman-genus3-review-2026-09-13.md §3) ends with a group-theoretic step:
- a finite-index subgroup `D''` of `π₁(UT Σ₂) ≤ Mod(R)` maps under the section into a direct product
  `Mod(R̃) × ⟨T_{c_T}⟩`;
- the exponent of the second factor is a homomorphism `ν : D'' → ℤ`;
- `ν` must vanish on the powers of the fiber class `T_c` that lie in `D''`.

The artifact derives the last point from the rational Euler class. This file proves it from Mathlib's transfer
homomorphism instead, for any group `E` with a central `z` some nonzero power of which lies in the commutator
subgroup. For `π₁(UT Σ₂)` the fiber class is central and `z^{±2}` is a product of two commutators.

* `transfer_eq_one_of_pow_mem_commutator`: the transfer of a homomorphism into a torsion-free commutative group
  kills `z`.
* `map_eq_one_of_mem_center_of_pow_mem_commutator`: such a homomorphism on a finite-index subgroup kills every power
  of `z` in its domain.
* `splitExponent`: if every `σ d` is `m * τ ^ n` with `m` in a subgroup `M` that commutes with `τ`, and `τ ^ n ∈ M`
  only for `n = 0`, then `d ↦ n` is a homomorphism.
* `mem_of_split_of_central`: in that situation `σ` sends every power of `z` in `D` into `M`.
-/

namespace GroupApproximation.BirmanGenusThree

section Transfer

variable {E : Type*} [Group E] {D : Subgroup E} [D.FiniteIndex] {A : Type*} [CommGroup A]

/-- The transfer of a homomorphism on a finite-index subgroup evaluates a central element through its
`index`-th power. -/
theorem transfer_eq_of_mem_center (ν : D →* A) {g : E} (hg : g ∈ Subgroup.center E)
    (hmem : g ^ D.index ∈ D) : ν.transfer g = ν ⟨g ^ D.index, hmem⟩ :=
  MonoidHom.transfer_eq_pow ν g fun k g₀ _ => by
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp (pow_mem hg k) g₀, inv_mul_cancel_left]

/-- An element with a nonzero power in the commutator subgroup is killed by every transfer into a torsion-free
commutative group. -/
theorem transfer_eq_one_of_pow_mem_commutator [IsMulTorsionFree A] (ν : D →* A) {z : E} {k : ℕ}
    (hk : k ≠ 0) (hzk : z ^ k ∈ commutator E) : ν.transfer z = 1 := by
  have h : ν.transfer (z ^ k) = 1 :=
    MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker ν.transfer hzk)
  rw [map_pow] at h
  exact (pow_eq_one_iff_left hk).mp h

/-- **Lemma C, transfer step.** Let `z` be central in `E` with a nonzero power in the commutator subgroup. A
homomorphism from a finite-index subgroup `D` into a torsion-free commutative group kills every power of `z` that
lies in `D`. -/
theorem map_eq_one_of_mem_center_of_pow_mem_commutator [IsMulTorsionFree A] (ν : D →* A) {z : E}
    (hz : z ∈ Subgroup.center E) {k : ℕ} (hk : k ≠ 0) (hzk : z ^ k ∈ commutator E) {N : ℕ}
    (hN : z ^ N ∈ D) : ν ⟨z ^ N, hN⟩ = 1 := by
  have hmem : (z ^ N) ^ D.index ∈ D := pow_mem hN _
  have h : ν.transfer (z ^ N) = 1 := by
    rw [map_pow, transfer_eq_one_of_pow_mem_commutator ν hk hzk, one_pow]
  rw [transfer_eq_of_mem_center ν (pow_mem hz N) hmem] at h
  have hpow : (⟨(z ^ N) ^ D.index, hmem⟩ : D) = ⟨z ^ N, hN⟩ ^ D.index :=
    Subtype.ext (Subgroup.coe_pow D ⟨z ^ N, hN⟩ D.index).symm
  rw [hpow, map_pow] at h
  exact (pow_eq_one_iff_left ‹D.FiniteIndex›.index_ne_zero).mp h

end Transfer

section Split

variable {G : Type*} [Group G] {M : Subgroup G} {τ : G}

/-- The exponent `n` in `g = m * τ ^ n` with `m ∈ M` is unique when `τ ^ n ∈ M` only for `n = 0`. -/
theorem splitExponent_unique (hdisj : ∀ n : ℤ, τ ^ n ∈ M → n = 0) {g : G} {n n' : ℤ}
    (h : g * (τ ^ n)⁻¹ ∈ M) (h' : g * (τ ^ n')⁻¹ ∈ M) : n = n' := by
  have hmem := mul_mem (inv_mem h) h'
  rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, ← zpow_sub] at hmem
  exact sub_eq_zero.mp (hdisj _ hmem)

/-- Exponents add along products when `M` commutes with `τ`. -/
theorem splitExponent_mul_mem (hcomm : ∀ m ∈ M, Commute m τ) {g g' : G} {n n' : ℤ}
    (h : g * (τ ^ n)⁻¹ ∈ M) (h' : g' * (τ ^ n')⁻¹ ∈ M) : g * g' * (τ ^ (n + n'))⁻¹ ∈ M := by
  have hc : Commute (g' * (τ ^ n')⁻¹) (τ ^ (-n)) := (hcomm _ h').zpow_right (-n)
  rw [zpow_neg] at hc
  have heq : g * g' * (τ ^ (n + n'))⁻¹ = g * (τ ^ n)⁻¹ * (g' * (τ ^ n')⁻¹) := by
    rw [mul_assoc g (τ ^ n)⁻¹, hc.symm.eq, zpow_add, mul_inv_rev]
    simp only [mul_assoc]
  rw [heq]
  exact mul_mem h h'

variable {E : Type*} [Group E] {D : Subgroup E}

/-- The exponent homomorphism `d ↦ n`, where `σ d = m * τ ^ n` with `m ∈ M`. -/
noncomputable def splitExponent (hcomm : ∀ m ∈ M, Commute m τ) (hdisj : ∀ n : ℤ, τ ^ n ∈ M → n = 0)
    (σ : D →* G) (hsplit : ∀ d : D, ∃ n : ℤ, σ d * (τ ^ n)⁻¹ ∈ M) : D →* Multiplicative ℤ :=
  MonoidHom.mk' (fun d => Multiplicative.ofAdd (hsplit d).choose) fun d d' => by
    show Multiplicative.ofAdd (hsplit (d * d')).choose =
      Multiplicative.ofAdd (hsplit d).choose * Multiplicative.ofAdd (hsplit d').choose
    rw [← ofAdd_add]
    congr 1
    refine splitExponent_unique hdisj (hsplit (d * d')).choose_spec ?_
    rw [map_mul]
    exact splitExponent_mul_mem hcomm (hsplit d).choose_spec (hsplit d').choose_spec

theorem splitExponent_apply (hcomm : ∀ m ∈ M, Commute m τ) (hdisj : ∀ n : ℤ, τ ^ n ∈ M → n = 0)
    (σ : D →* G) (hsplit : ∀ d : D, ∃ n : ℤ, σ d * (τ ^ n)⁻¹ ∈ M) (d : D) :
    splitExponent hcomm hdisj σ hsplit d = Multiplicative.ofAdd (hsplit d).choose :=
  rfl

/-- **Lemma C, algebraic core.** Let `z` be central in `E` with a nonzero power in the commutator subgroup, let
`D ≤ E` have finite index, and let `σ : D →* G` be such that every `σ d` is `m * τ ^ n` with `m ∈ M`, where `M`
commutes with `τ` and `τ ^ n ∈ M` only for `n = 0`. Then `σ` sends every power of `z` that lies in `D` into `M`. -/
theorem mem_of_split_of_central [D.FiniteIndex] (hcomm : ∀ m ∈ M, Commute m τ)
    (hdisj : ∀ n : ℤ, τ ^ n ∈ M → n = 0) (σ : D →* G)
    (hsplit : ∀ d : D, ∃ n : ℤ, σ d * (τ ^ n)⁻¹ ∈ M) {z : E} (hz : z ∈ Subgroup.center E) {k : ℕ}
    (hk : k ≠ 0) (hzk : z ^ k ∈ commutator E) {N : ℕ} (hN : z ^ N ∈ D) : σ ⟨z ^ N, hN⟩ ∈ M := by
  have h1 :=
    map_eq_one_of_mem_center_of_pow_mem_commutator (splitExponent hcomm hdisj σ hsplit) hz hk hzk hN
  rw [splitExponent_apply, ofAdd_eq_one] at h1
  have h2 := (hsplit ⟨z ^ N, hN⟩).choose_spec
  rwa [h1, zpow_zero, inv_one, mul_one] at h2

end Split

end GroupApproximation.BirmanGenusThree
