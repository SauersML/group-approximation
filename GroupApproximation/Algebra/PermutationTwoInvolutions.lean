import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Every permutation of a finite type is a product of two involutions

This is the one input the consumption half of `hBNG` needs, and mathlib does
not have it at the pin: `isConj_iff_cycleType_eq` together with `cycleType_inv`
produces an element conjugating a permutation to its inverse, but says nothing
about that element being an involution, and involutivity is the entire content.

The route is the classical one.  A cycle is reversed by the map that sends
`σ^k(x₀)` to `σ^{-k}(x₀)`, which is an involution because inversion is one on
the cyclic group `⟨σ⟩`; disjoint cycles are reversed independently; and a
reverser `v` for `a` turns into the factorization `a = (a·v)·v`, both factors
being involutions because `v a v = a⁻¹`.

## What is proved

* `rev` — the reversal of a cycle, built by transporting inversion on
  `Subgroup.zpowers σ` across `IsCycle.zpowersEquivSupport` and extending by the
  identity off the support.  `rev_rev`, `rev_mul_eq`, `rev_support`.
* `exists_reverser` — every permutation `a` has an involution `v` supported in
  `supp a` with `v a v = a⁻¹`.
* `exists_two_involutions` — hence `a = u·v` with `u`, `v` involutions
  supported in `supp a`.

## Where it is used

Nowhere yet.  It is the missing step of the route recorded in
`Algebra/AlternatingBoundedNormalGeneration.lean`: with it, an even permutation
splits as two involutions of equal transposition-count parity, each of which
cuts into blocks of at most `|supp s|/6` disjoint transpositions, and a block
with `2k` transpositions has cycle type `2^k + 2^k`, which
`AlternatingDoubledTransport.isBoundedConjProduct_two_of_cycleType_doubled`
reaches in two conjugates.  Blocking, the parity repair and the count in `δ` are
still to be written; this file closes only the input that mathlib lacks.
-/

namespace GroupApproximation
namespace PermutationTwoInvolutions

open Equiv

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] [Fintype α] in
/-- Elements of `⟨σ⟩` commute with `σ`.  Stated outside the cycle section
because it needs neither the cycle hypothesis nor the finiteness of `α`. -/
theorem zpowers_commute {σ : Equiv.Perm α} (τ : Subgroup.zpowers σ) :
    Commute (τ : Equiv.Perm α) σ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp τ.2
  rw [← hk]
  exact (Commute.refl σ).zpow_left k

/-! ## The powers that reach a point of the support -/

section Cycle

variable {σ : Equiv.Perm α} (hσ : σ.IsCycle)

/-- The base point supplied by the cycle property. -/
noncomputable abbrev base : α := Classical.choose hσ

/-- Every element of `⟨σ⟩` is carried to the point it sends the base point to.
This is `IsCycle.zpowersEquivSupport` read off its definition. -/
@[simp] theorem coe_zpowersEquivSupport (τ : Subgroup.zpowers σ) :
    ((hσ.zpowersEquivSupport τ : σ.support) : α)
      = (τ : Equiv.Perm α) (base hσ) := rfl

/-- The power of `σ` carrying the base point to a given point of the support. -/
noncomputable def power (y : σ.support) : Subgroup.zpowers σ :=
  hσ.zpowersEquivSupport.symm y

theorem power_apply_base (y : σ.support) :
    ((power hσ y : Equiv.Perm α)) (base hσ) = (y : α) := by
  have h := coe_zpowersEquivSupport hσ (power hσ y)
  have he : hσ.zpowersEquivSupport (power hσ y) = y :=
    Equiv.apply_symm_apply _ _
  rw [he] at h
  exact h.symm

theorem power_of_apply_base (τ : Subgroup.zpowers σ)
    (h : (τ : Equiv.Perm α) (base hσ) ∈ σ.support) :
    power hσ ⟨(τ : Equiv.Perm α) (base hσ), h⟩ = τ := by
  have hτ : hσ.zpowersEquivSupport τ
      = ⟨(τ : Equiv.Perm α) (base hσ), h⟩ :=
    Subtype.ext (coe_zpowersEquivSupport hσ τ)
  show hσ.zpowersEquivSupport.symm ⟨(τ : Equiv.Perm α) (base hσ), h⟩ = τ
  rw [← hτ, Equiv.symm_apply_apply]

/-! ## The reversal of a cycle -/

/-- **The reversal of a cycle**: inversion on `⟨σ⟩`, transported to the support
along `IsCycle.zpowersEquivSupport`, and the identity elsewhere.  It sends
`σ^k(x₀)` to `σ^{-k}(x₀)`. -/
noncomputable def rev : Equiv.Perm α :=
  Equiv.Perm.subtypeCongr (p := fun x => x ∈ σ.support)
    (hσ.zpowersEquivSupport.symm.trans
      ((Equiv.inv ↥(Subgroup.zpowers σ)).trans hσ.zpowersEquivSupport))
    (Equiv.refl _)

theorem rev_apply_of_mem {y : α} (hy : y ∈ σ.support) :
    rev hσ y = ((power hσ ⟨y, hy⟩)⁻¹ : Equiv.Perm α) (base hσ) := by
  rw [rev, Equiv.Perm.subtypeCongr.left_apply _ _ hy]
  exact coe_zpowersEquivSupport hσ _

theorem rev_apply_of_not_mem {y : α} (hy : y ∉ σ.support) : rev hσ y = y := by
  rw [rev, Equiv.Perm.subtypeCongr.right_apply _ _ hy]
  rfl

theorem rev_mem_support {y : α} (hy : y ∈ σ.support) :
    rev hσ y ∈ σ.support := by
  rw [rev, Equiv.Perm.subtypeCongr.left_apply _ _ hy]
  exact Subtype.prop _

/-- The power reaching `rev y` is the inverse of the power reaching `y`. -/
theorem power_rev {y : α} (hy : y ∈ σ.support) :
    power hσ ⟨rev hσ y, rev_mem_support hσ hy⟩ = (power hσ ⟨y, hy⟩)⁻¹ := by
  have h := rev_apply_of_mem hσ hy
  have hmem : ((power hσ ⟨y, hy⟩)⁻¹ : Equiv.Perm α) (base hσ) ∈ σ.support := by
    rw [← h]
    exact rev_mem_support hσ hy
  have heq : (⟨rev hσ y, rev_mem_support hσ hy⟩ : σ.support)
      = ⟨((power hσ ⟨y, hy⟩)⁻¹ : Equiv.Perm α) (base hσ), hmem⟩ :=
    Subtype.ext h
  rw [heq]
  exact power_of_apply_base hσ ((power hσ ⟨y, hy⟩)⁻¹) hmem

/-- **The reversal is an involution.** -/
theorem rev_rev (y : α) : rev hσ (rev hσ y) = y := by
  by_cases hy : y ∈ σ.support
  · -- `rev_apply_of_mem` puts the inverse in `Equiv.Perm α`, *outside* the
    -- coercion, so the subgroup-level `inv_inv` cannot match.  Push the
    -- coercion through the inverse first, then cancel in `Equiv.Perm α`.
    rw [rev_apply_of_mem hσ (rev_mem_support hσ hy), power_rev hσ hy,
      Subgroup.coe_inv, inv_inv]
    exact power_apply_base hσ ⟨y, hy⟩
  · rw [rev_apply_of_not_mem hσ hy, rev_apply_of_not_mem hσ hy]

theorem rev_mul_rev : rev hσ * rev hσ = 1 := by
  ext y
  exact rev_rev hσ y

/-- **The reversal conjugates the cycle to its inverse**, in the form
`v σ = σ⁻¹ v`. -/
theorem rev_mul_eq : rev hσ * σ = σ⁻¹ * rev hσ := by
  ext y
  show rev hσ (σ y) = σ⁻¹ (rev hσ y)
  by_cases hy : y ∈ σ.support
  · have hσy : σ y ∈ σ.support := Equiv.Perm.apply_mem_support.mpr hy
    -- the power reaching `σ y` is `σ` times the power reaching `y`
    have hmul : ((⟨σ, Subgroup.mem_zpowers σ⟩ * power hσ ⟨y, hy⟩ :
        Subgroup.zpowers σ) : Equiv.Perm α) (base hσ) = σ y := by
      show (σ * (power hσ ⟨y, hy⟩ : Equiv.Perm α)) (base hσ) = σ y
      rw [Equiv.Perm.mul_apply, power_apply_base hσ ⟨y, hy⟩]
    have hpow : power hσ ⟨σ y, hσy⟩
        = ⟨σ, Subgroup.mem_zpowers σ⟩ * power hσ ⟨y, hy⟩ := by
      have hmem : ((⟨σ, Subgroup.mem_zpowers σ⟩ * power hσ ⟨y, hy⟩ :
          Subgroup.zpowers σ) : Equiv.Perm α) (base hσ) ∈ σ.support := by
        rw [hmul]
        exact hσy
      have heq : (⟨σ y, hσy⟩ : σ.support)
          = ⟨((⟨σ, Subgroup.mem_zpowers σ⟩ * power hσ ⟨y, hy⟩ :
              Subgroup.zpowers σ) : Equiv.Perm α) (base hσ), hmem⟩ :=
        Subtype.ext hmul.symm
      rw [heq]
      exact power_of_apply_base hσ _ hmem
    rw [rev_apply_of_mem hσ hσy, rev_apply_of_mem hσ hy, hpow]
    show ((⟨σ, Subgroup.mem_zpowers σ⟩ * power hσ ⟨y, hy⟩ :
        Subgroup.zpowers σ)⁻¹ : Equiv.Perm α) (base hσ)
      = σ⁻¹ (((power hσ ⟨y, hy⟩)⁻¹ : Equiv.Perm α) (base hσ))
    have hcomm : ((power hσ ⟨y, hy⟩)⁻¹ : Equiv.Perm α) * σ⁻¹
        = σ⁻¹ * ((power hσ ⟨y, hy⟩)⁻¹ : Equiv.Perm α) :=
      ((zpowers_commute (power hσ ⟨y, hy⟩)).inv_left.inv_right).eq
    calc ((⟨σ, Subgroup.mem_zpowers σ⟩ * power hσ ⟨y, hy⟩ :
            Subgroup.zpowers σ)⁻¹ : Equiv.Perm α) (base hσ)
        = (((power hσ ⟨y, hy⟩)⁻¹ : Equiv.Perm α) * σ⁻¹) (base hσ) := by
          simp
      _ = (σ⁻¹ * ((power hσ ⟨y, hy⟩)⁻¹ : Equiv.Perm α)) (base hσ) := by
          rw [hcomm]
      _ = σ⁻¹ (((power hσ ⟨y, hy⟩)⁻¹ : Equiv.Perm α) (base hσ)) :=
          Equiv.Perm.mul_apply _ _ _
  · have hfix : σ y = y := by
      by_contra hcon
      exact hy (Equiv.Perm.mem_support.mpr hcon)
    have hfix' : σ⁻¹ y = y := Equiv.Perm.inv_eq_iff_eq.mpr hfix.symm
    rw [hfix, rev_apply_of_not_mem hσ hy, hfix']

theorem rev_support : (rev hσ).support ⊆ σ.support := by
  intro y hy
  by_contra hcon
  exact (Equiv.Perm.mem_support.mp hy) (rev_apply_of_not_mem hσ hcon)

end Cycle

/-! ## Every permutation has an involutive reverser -/

/-- **Every permutation is reversed by an involution supported in its
support.**  Cycles are reversed by `rev`, and disjoint cycles independently:
the two reversers commute with each other and with the other's cycle, because
their supports are disjoint. -/
theorem exists_reverser (a : Equiv.Perm α) :
    ∃ v : Equiv.Perm α, v * v = 1 ∧ v * a = a⁻¹ * v ∧ v.support ⊆ a.support := by
  induction a using Equiv.Perm.cycle_induction_on with
  | base_one => exact ⟨1, by simp, by simp, by simp⟩
  | base_cycles σ hσ =>
      exact ⟨rev hσ, rev_mul_rev hσ, rev_mul_eq hσ, rev_support hσ⟩
  | induction_disjoint σ τ hd _ ihσ ihτ =>
      obtain ⟨u, hu2, huc, husupp⟩ := ihσ
      obtain ⟨w, hw2, hwc, hwsupp⟩ := ihτ
      have hdsupp : Disjoint σ.support τ.support :=
        Equiv.Perm.disjoint_iff_disjoint_support.mp hd
      have hduw : Equiv.Perm.Disjoint u w :=
        Equiv.Perm.disjoint_iff_disjoint_support.mpr
          (Finset.disjoint_of_subset_left husupp
            (Finset.disjoint_of_subset_right hwsupp hdsupp))
      have hduτ : Equiv.Perm.Disjoint u τ :=
        Equiv.Perm.disjoint_iff_disjoint_support.mpr
          (Finset.disjoint_of_subset_left husupp hdsupp)
      have hdwσ : Equiv.Perm.Disjoint w σ :=
        Equiv.Perm.disjoint_iff_disjoint_support.mpr
          (Finset.disjoint_of_subset_left hwsupp hdsupp.symm)
      refine ⟨u * w, ?_, ?_, ?_⟩
      · calc u * w * (u * w) = u * (w * u) * w := by group
          _ = u * (u * w) * w := by rw [hduw.commute.symm.eq]
          _ = (u * u) * (w * w) := by group
          _ = 1 := by rw [hu2, hw2, mul_one]
      · calc u * w * (σ * τ) = u * (w * σ) * τ := by group
          _ = u * (σ * w) * τ := by rw [hdwσ.commute.eq]
          _ = (u * σ) * (w * τ) := by group
          _ = (σ⁻¹ * u) * (τ⁻¹ * w) := by rw [huc, hwc]
          _ = σ⁻¹ * (u * τ⁻¹) * w := by group
          _ = σ⁻¹ * (τ⁻¹ * u) * w := by rw [hduτ.inv_right.commute.eq]
          _ = (σ⁻¹ * τ⁻¹) * (u * w) := by group
          _ = (τ⁻¹ * σ⁻¹) * (u * w) := by
                rw [hd.inv_left.inv_right.commute.eq]
          _ = (σ * τ)⁻¹ * (u * w) := by rw [mul_inv_rev]
      · rw [hd.support_mul]
        intro x hx
        have hx' : x ∈ u.support ∪ w.support :=
          Equiv.Perm.support_mul_le u w hx
        rcases Finset.mem_union.mp hx' with h | h
        · exact Finset.mem_union_left _ (husupp h)
        · exact Finset.mem_union_right _ (hwsupp h)

/-- **Every permutation of a finite type is a product of two involutions
supported in its support.** -/
theorem exists_two_involutions (a : Equiv.Perm α) :
    ∃ u v : Equiv.Perm α, u * u = 1 ∧ v * v = 1 ∧ a = u * v ∧
      u.support ⊆ a.support ∧ v.support ⊆ a.support := by
  obtain ⟨v, hv2, hvc, hvsupp⟩ := exists_reverser a
  have hconj : v * a * v = a⁻¹ := by
    calc v * a * v = a⁻¹ * v * v := by rw [hvc]
      _ = a⁻¹ * (v * v) := by group
      _ = a⁻¹ := by rw [hv2, mul_one]
  refine ⟨a * v, v, ?_, hv2, ?_, ?_, hvsupp⟩
  · calc a * v * (a * v) = a * (v * a * v) := by group
      _ = a * a⁻¹ := by rw [hconj]
      _ = 1 := mul_inv_cancel a
  · calc a = a * (v * v) := by rw [hv2, mul_one]
      _ = a * v * v := by group
  · intro x hx
    have hx' : x ∈ a.support ∪ v.support := Equiv.Perm.support_mul_le a v hx
    rcases Finset.mem_union.mp hx' with h | h
    · exact h
    · exact hvsupp h

/-- **The two factors of an even permutation have the same sign.**  Signs in
`ℤˣ` are their own inverses, so a product equal to `1` forces the two factors to
agree.

This is the parity fact the blocking step needs: the two involutions of an even
permutation have transposition counts of equal parity, so the single spare
transposition that makes one leftover block even makes the other one even
too. -/
theorem sign_eq_of_sign_mul_eq_one {u v : Equiv.Perm α}
    (h : Equiv.Perm.sign (u * v) = 1) :
    Equiv.Perm.sign u = Equiv.Perm.sign v := by
  have h1 : Equiv.Perm.sign u * Equiv.Perm.sign v = 1 := by
    rw [← Equiv.Perm.sign_mul]
    exact h
  have h2 : Equiv.Perm.sign u * Equiv.Perm.sign u = 1 :=
    Int.units_mul_self _
  exact (mul_left_cancel (h1.trans h2.symm)).symm

end PermutationTwoInvolutions
end GroupApproximation
