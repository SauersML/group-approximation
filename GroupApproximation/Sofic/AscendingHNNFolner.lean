import GroupApproximation.Sofic.SoficTelescope
import GroupApproximation.Sofic.MarkedCompressionGroup
import Mathlib.Order.SymmDiff

/-!
# Section 10: explicit Følner sets for the ascending-HNN coset action

Monod--Popa prove co-amenability of the base in an ascending HNN extension with
invariant means.  Here is the concrete Følner proof: the coset space contains
the ray `x_j = t^{-j} Γ`, deep telescope elements fix its tail, and every group
element eventually acts on the ray as the height translation alone.  Intervals
of the ray are therefore Følner sets: translation moves an interval by a bounded
amount, so the symmetric difference is bounded while the interval grows.

The ray is indexed by `ℤ`, which costs nothing and removes the case analysis at
the near end.

The co-amenability theorem is Monod--Popa's; that it applies naturally to this
ascending-HNN instance, through the directed union `N = ⋃ t^{-n} Γ t^n` with
`G = N ⋊ ⟨t⟩`, was pointed out by Fournier-Facio.
-/

namespace GroupApproximation

namespace AscendingHNNFolner

open MappingTelescope MarkedCompression SemidirectProduct

open scoped symmDiff

universe u

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The ray of coset points `x_j = t^{-j} Γ`. -/
def ray (j : ℤ) : Cosets α hα :=
  QuotientGroup.mk ((tVertical α hα) ^ (-j))

/-! ## Heights -/

@[simp] theorem right_iotaVertical (γ : Γ) :
    (iotaVertical α hα γ).right = 1 := rfl

theorem right_tVertical_zpow (j : ℤ) :
    ((tVertical α hα) ^ j).right = Multiplicative.ofAdd j := by
  have hpow : (tVertical α hα) ^ j
      = (inr (Multiplicative.ofAdd 1) : Vertical α hα) ^ j := rfl
  rw [hpow, ← map_zpow]
  show (Multiplicative.ofAdd (1 : ℤ)) ^ j = Multiplicative.ofAdd j
  rw [← ofAdd_zsmul]
  simp

theorem ray_injective : Function.Injective (ray α hα) := by
  intro j₁ j₂ h
  have hmem := (QuotientGroup.eq (s := (iotaVertical α hα).range)).mp h
  obtain ⟨γ, hγ⟩ := hmem
  have hright := congrArg SemidirectProduct.right hγ
  rw [right_iotaVertical] at hright
  have hcalc : (((tVertical α hα) ^ (-j₁))⁻¹ * (tVertical α hα) ^ (-j₂)).right
      = Multiplicative.ofAdd (j₁ - j₂) := by
    rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      right_tVertical_zpow, right_tVertical_zpow]
    rw [← ofAdd_neg, ← ofAdd_add]
    congr 1
    ring
  rw [hcalc] at hright
  have hzero : (0 : ℤ) = j₁ - j₂ := by
    simpa using congrArg Multiplicative.toAdd hright
  omega

/-! ## The action on the ray -/

theorem tVertical_zpow_smul_ray (q j : ℤ) :
    ((tVertical α hα) ^ q) • ray α hα j = ray α hα (j - q) := by
  simp only [ray]
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← zpow_add]
  congr 2
  ring

include hα in
/-- Level `n` of the telescope, viewed vertically, is the base conjugated by
the `n`-th power of the stable letter. -/
theorem inl_level_eq_conj (n : ℕ) (x : Γ) :
    (inl (level α hα n x) : Vertical α hα)
      = ((tVertical α hα) ^ (n : ℤ))⁻¹ * iotaVertical α hα x
        * (tVertical α hα) ^ (n : ℤ) := by
  induction n with
  | zero => simp [iotaVertical]
  | succ n ih =>
      rw [inl_level_succ, ih]
      have hstep : ((tVertical α hα) ^ ((n : ℤ) + 1))
          = (tVertical α hα) ^ (n : ℤ) * tVertical α hα := by
        rw [zpow_add_one]
      push_cast
      rw [hstep, mul_inv_rev]
      group

include hα in
/-- Conjugating the base by a nonnegative power of the stable letter stays in
the base: this is the compression relation iterated. -/
theorem tVertical_pow_conj_mem (n : ℕ) (x : Γ) :
    (tVertical α hα) ^ (n : ℤ) * iotaVertical α hα x
      * ((tVertical α hα) ^ (n : ℤ))⁻¹ ∈ (iotaVertical α hα).range := by
  induction n with
  | zero => exact ⟨x, by simp⟩
  | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      refine ⟨α y, ?_⟩
      have hstep : ((tVertical α hα) ^ ((n : ℕ) + 1 : ℤ))
          = tVertical α hα * (tVertical α hα) ^ (n : ℤ) := by
        rw [add_comm, zpow_add, zpow_one]
      push_cast
      rw [hstep, mul_inv_rev, ← vertical_compress α hα y, hy]
      group

include hα in
/-- **Lemma 10.1 and 10.2 combined.**  Every group element acts on the far end
of the ray as the height translation alone. -/
theorem smul_ray_eq (g : Vertical α hα) :
    ∃ M : ℕ, ∀ j : ℤ, (M : ℤ) ≤ j - Multiplicative.toAdd g.right →
      g • ray α hα j = ray α hα (j - Multiplicative.toAdd g.right) := by
  obtain ⟨M, x, hMx⟩ := exists_level_repr α hα g.left
  refine ⟨M, fun j hj => ?_⟩
  set q : ℤ := Multiplicative.toAdd g.right with hq
  -- split `g` into its lamp and height parts
  have hsplit : g = inl g.left * (tVertical α hα) ^ q := by
    have hpow : (tVertical α hα) ^ q
        = (inr (Multiplicative.ofAdd q) : Vertical α hα) := by
      show ((inr (Multiplicative.ofAdd 1) : Vertical α hα)) ^ q = _
      rw [← map_zpow]
      congr 1
      rw [← ofAdd_zsmul]
      simp
    rw [hpow]
    have hright : Multiplicative.ofAdd q = g.right := by
      rw [hq]
      simp
    rw [hright]
    exact (SemidirectProduct.inl_left_mul_inr_right g).symm
  rw [hsplit, mul_smul, tVertical_zpow_smul_ray]
  -- the level element fixes the far end of the ray
  set k : ℤ := j - q with hk
  have hMk : (M : ℤ) ≤ k := hj
  rw [← hMx]
  simp only [ray]
  rw [MulAction.Quotient.smul_mk, smul_eq_mul]
  refine (QuotientGroup.eq (s := (iotaVertical α hα).range)).mpr ?_
  -- the conjugate lands in the base because `k - M ≥ 0`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = (M : ℤ) + m :=
    ⟨(k - M).toNat, by omega⟩
  have hconj := tVertical_pow_conj_mem α hα m x
  obtain ⟨y, hy⟩ := hconj
  have hexp : (tVertical α hα) ^ (-k)
      = ((tVertical α hα) ^ (M : ℤ))⁻¹ * ((tVertical α hα) ^ (m : ℤ))⁻¹ := by
    rw [← zpow_neg, ← zpow_neg, ← zpow_add]
    congr 1
    omega
  refine ⟨y⁻¹, ?_⟩
  rw [map_inv, hy, inl_level_eq_conj α hα M x, hexp]
  group

/-! ## Interval Følner sets -/

/-- Two integer intervals of the same length differ, symmetrically, by at most
twice the shift. -/
theorem card_symmDiff_Ico_le (a b : ℤ) (L : ℕ) :
    ((Finset.Ico a (a + L)) ∆ (Finset.Ico b (b + L))).card
      ≤ 2 * (a - b).natAbs := by
  classical
  have hsub : (Finset.Ico a (a + L)) ∆ (Finset.Ico b (b + L))
      ⊆ (Finset.Ico (min a b) (max a b))
        ∪ (Finset.Ico (min a b + L) (max a b + L)) := by
    intro x hx
    rw [Finset.mem_symmDiff] at hx
    simp only [Finset.mem_union, Finset.mem_Ico] at hx ⊢
    omega
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
    (Finset.Ico (min a b) (max a b))
    (Finset.Ico (min a b + L) (max a b + L))
  rw [Int.card_Ico, Int.card_Ico] at hunion
  omega

/-- **Theorem 10.3.**  Intervals of the ray are Følner sets for the coset
action: every element of a prescribed finite set moves a long interval by a
bounded amount. -/
theorem exists_folner_interval [DecidableEq (Cosets α hα)]
    (F : Finset (Vertical α hα)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (R : ℤ) (L : ℕ), 0 < L ∧ ∀ g ∈ F,
      (((((Finset.Ico R (R + L)).image (ray α hα)).image (fun x => g • x)) ∆
        ((Finset.Ico R (R + L)).image (ray α hα))).card : ℝ) < ε * L := by
  classical
  choose Mg hMg using fun g : Vertical α hα => smul_ray_eq α hα g
  set M : ℕ := F.sup Mg with hM
  set Q : ℕ := F.sup (fun g => (Multiplicative.toAdd g.right).natAbs) with hQ
  set R : ℤ := (M : ℤ) + (Q : ℤ) with hR
  obtain ⟨L, hL⟩ := exists_nat_gt ((2 * Q + 1) / ε)
  have hLpos : 0 < L := by
    by_contra hcon
    push Not at hcon
    have hL0 : L = 0 := by omega
    rw [hL0] at hL
    have : 0 < (2 * (Q : ℝ) + 1) / ε := by positivity
    simp only [Nat.cast_zero] at hL
    linarith
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hLbig : 2 * (Q : ℝ) < ε * L := by
    rw [div_lt_iff₀ hε] at hL
    linarith
  refine ⟨R, L, hLpos, fun g hg => ?_⟩
  set q : ℤ := Multiplicative.toAdd g.right with hq
  -- the translation is exact on the whole interval
  have htrans : ∀ j ∈ Finset.Ico R (R + L), g • ray α hα j = ray α hα (j - q) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    refine hMg g j ?_
    have h1 : (Mg g : ℤ) ≤ (M : ℤ) := by
      exact_mod_cast Finset.le_sup (f := Mg) hg
    have h2 : q.natAbs ≤ Q := Finset.le_sup (f := fun g =>
      (Multiplicative.toAdd g.right).natAbs) hg
    have h3 : q ≤ (q.natAbs : ℤ) := Int.le_natAbs
    have h4 : (q.natAbs : ℤ) ≤ (Q : ℤ) := by exact_mod_cast h2
    omega
  -- the translated interval
  have himage : (((Finset.Ico R (R + L)).image (ray α hα)).image (fun x => g • x))
      = (Finset.Ico (R - q) (R - q + L)).image (ray α hα) := by
    rw [Finset.image_image]
    ext y
    simp only [Finset.mem_image, Finset.mem_Ico, Function.comp_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨j - q, by omega, ?_⟩
      exact (htrans j (Finset.mem_Ico.mpr ⟨hj.1, hj.2⟩)).symm ▸ rfl
    · rintro ⟨i, hi, rfl⟩
      refine ⟨i + q, by omega, ?_⟩
      have := htrans (i + q) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      simpa using this
  rw [himage]
  -- the symmetric difference is carried by the interval symmetric difference
  have hsub : ((Finset.Ico (R - q) (R - q + L)).image (ray α hα)) ∆
      ((Finset.Ico R (R + L)).image (ray α hα))
      ⊆ ((Finset.Ico (R - q) (R - q + L)) ∆ (Finset.Ico R (R + L))).image
        (ray α hα) := by
    intro y hy
    rw [Finset.mem_symmDiff] at hy
    simp only [Finset.mem_image] at hy ⊢
    rcases hy with ⟨⟨j, hj, rfl⟩, hnot⟩ | ⟨⟨j, hj, rfl⟩, hnot⟩
    · refine ⟨j, Finset.mem_symmDiff.mpr (Or.inl ⟨hj, ?_⟩), rfl⟩
      intro hcon
      exact hnot ⟨j, hcon, rfl⟩
    · refine ⟨j, Finset.mem_symmDiff.mpr (Or.inr ⟨hj, ?_⟩), rfl⟩
      intro hcon
      exact hnot ⟨j, hcon, rfl⟩
  have hcard : ((((Finset.Ico (R - q) (R - q + L)).image (ray α hα)) ∆
      ((Finset.Ico R (R + L)).image (ray α hα))).card : ℝ) ≤ 2 * (Q : ℝ) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := (Finset.Ico (R - q) (R - q + L)) ∆
      (Finset.Ico R (R + L))) (f := ray α hα)
    have h3 := card_symmDiff_Ico_le (R - q) R L
    have h4 : ((R - q) - R).natAbs = q.natAbs := by
      have : (R - q) - R = -q := by ring
      rw [this, Int.natAbs_neg]
    rw [h4] at h3
    have h5 : q.natAbs ≤ Q := Finset.le_sup (f := fun g =>
      (Multiplicative.toAdd g.right).natAbs) hg
    have hchain : (((Finset.Ico (R - q) (R - q + L)).image (ray α hα)) ∆
        ((Finset.Ico R (R + L)).image (ray α hα))).card ≤ 2 * Q := by
      omega
    exact_mod_cast (by exact_mod_cast hchain : ((((Finset.Ico (R - q)
      (R - q + L)).image (ray α hα)) ∆ ((Finset.Ico R (R + L)).image
        (ray α hα))).card : ℝ) ≤ ((2 * Q : ℕ) : ℝ))
  linarith

end AscendingHNNFolner

end GroupApproximation
