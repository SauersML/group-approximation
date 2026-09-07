import GroupApproximation.Algebra.PurelyInfiniteUnitInfinite

/-!
# Arbitrarily many pairwise orthogonal copies of `1`

`AGPStepOne` (AGP Theorem 2.4 Step 1) needs, for a nonzero idempotent `e` and
`n ≥ 2`, orthogonal idempotents `r_2, …, r_n ≤ e - f`, **each equivalent to
`1`**.  Comparability (`exists_idempotentLE_equivalent`) embeds one prescribed
idempotent inside one ambient idempotent, but naively peeling copies off a
shrinking remainder one at a time has a real gap: nothing says the embedded
copy is a *proper* sub-idempotent, so the remainder could vanish before `n`
copies are found.

This module sidesteps that: it builds `n` pairwise orthogonal copies of `1`
**inside `1` itself**, all at once, with no shrinking remainder to worry about.

## The construction

`isInfiniteIdempotent_one` gives `1 = f₀ + g₀` with `f₀ ~ 1` and `g₀ ≠ 0`, and
a normalised isometry pair `s₀, t₀` with `t₀ * s₀ = 1`, `s₀ * t₀ = f₀`.  Exactly
as in `Algebra/PurelyInfiniteSandwich.lean`'s own argument, `g₀ * s₀ = 0` and
`t₀ * g₀ = 0`, and these two relations alone make the shifted elements

    `g k := s₀ ^ k * g₀ * t₀ ^ k`

pairwise orthogonal idempotents, each equivalent to `g₀` (via `t₀ ^ k * s₀ ^ k
= 1`, so nonzero), for every `k : ℕ`.  Picking `n` of them, `g 0, …, g (n - 1)`,
gives `n` pairwise orthogonal **nonzero** idempotents with no further work: no
splitting is needed, since each `g k` is used exactly once.

Comparability then embeds a copy of `1` inside *each* `g k` independently —
independence is exactly what orthogonality of the `g k` buys, so there is no
shrinking remainder and no risk of running out of room.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

section ShiftedCopies

variable {s t g₀ : R}

/-- `t ^ k * s ^ k = 1` for every `k`, including `k = 0`. -/
theorem pow_mul_self_eq_one (hts : t * s = 1) (hes : (1 : R) * s = s) :
    ∀ k : ℕ, t ^ k * s ^ k = 1
  | 0 => by simp
  | (m + 1) => pow_mul_self_eq hts hes m

/-- The `k`-th shifted copy of `g₀` is idempotent. -/
theorem isIdempotentElem_shiftedCopy (hts : t * s = 1) (hes : (1 : R) * s = s)
    (hg₀ : IsIdempotentElem g₀) (k : ℕ) :
    IsIdempotentElem (s ^ k * g₀ * t ^ k) := by
  show (s ^ k * g₀ * t ^ k) * (s ^ k * g₀ * t ^ k) = s ^ k * g₀ * t ^ k
  have h1 : (s ^ k * g₀ * t ^ k) * (s ^ k * g₀ * t ^ k)
      = s ^ k * (g₀ * (t ^ k * s ^ k) * g₀) * t ^ k := by noncomm_ring
  rw [h1, pow_mul_self_eq_one hts hes k]
  have h2 : s ^ k * (g₀ * 1 * g₀) * t ^ k = s ^ k * (g₀ * g₀) * t ^ k := by
    noncomm_ring
  rw [h2, hg₀]

/-- The `k`-th shifted copy of `g₀` is equivalent to `g₀`. -/
theorem isEquivalentIdempotent_shiftedCopy (hts : t * s = 1)
    (hes : (1 : R) * s = s) (k : ℕ) :
    IsEquivalentIdempotent R (s ^ k * g₀ * t ^ k) g₀ := by
  refine ⟨s ^ k * g₀, t ^ k, rfl, ?_⟩
  have h1 : t ^ k * (s ^ k * g₀) = (t ^ k * s ^ k) * g₀ := by noncomm_ring
  rw [h1, pow_mul_self_eq_one hts hes k, one_mul]

/-- **Pairwise orthogonality of the shifted copies.**  Uses only `g₀ * s = 0`
and `t * g₀ = 0`. -/
theorem shiftedCopy_orthogonal (hts : t * s = 1) (hes : (1 : R) * s = s)
    (hgs : g₀ * s = 0) (htg : t * g₀ = 0) {i j : ℕ} (hij : i ≠ j) :
    (s ^ i * g₀ * t ^ i) * (s ^ j * g₀ * t ^ j) = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hsplit : t ^ i * s ^ j = s ^ (j - i) := by
      have hji : j = i + (j - i) := by omega
      calc t ^ i * s ^ j = t ^ i * s ^ (i + (j - i)) := by rw [← hji]
        _ = t ^ i * (s ^ i * s ^ (j - i)) := by rw [pow_add]
        _ = (t ^ i * s ^ i) * s ^ (j - i) := by noncomm_ring
        _ = 1 * s ^ (j - i) := by rw [pow_mul_self_eq_one hts hes i]
        _ = s ^ (j - i) := one_mul _
    have hji1 : j - i = (j - i - 1) + 1 := by omega
    have hz : g₀ * s ^ (j - i) = 0 := by
      rw [hji1]; exact mul_pow_eq_zero_left hgs (j - i - 1)
    calc s ^ i * g₀ * t ^ i * (s ^ j * g₀ * t ^ j)
        = s ^ i * (g₀ * (t ^ i * s ^ j) * g₀) * t ^ j := by noncomm_ring
      _ = s ^ i * (g₀ * s ^ (j - i) * g₀) * t ^ j := by rw [hsplit]
      _ = s ^ i * (0 * g₀) * t ^ j := by rw [hz]
      _ = 0 := by simp
  · have hsplit : t ^ i * s ^ j = t ^ (i - j) := by
      have hij' : i = j + (i - j) := by omega
      calc t ^ i * s ^ j = t ^ (j + (i - j)) * s ^ j := by rw [← hij']
        _ = (t ^ j * t ^ (i - j)) * s ^ j := by rw [pow_add]
        _ = (t ^ (i - j) * t ^ j) * s ^ j := by rw [← pow_add, ← pow_add, Nat.add_comm]
        _ = t ^ (i - j) * (t ^ j * s ^ j) := by noncomm_ring
        _ = t ^ (i - j) * 1 := by rw [pow_mul_self_eq_one hts hes j]
        _ = t ^ (i - j) := mul_one _
    have hij1 : i - j = (i - j - 1) + 1 := by omega
    have hz : t ^ (i - j) * g₀ = 0 := by
      rw [hij1]; exact pow_mul_eq_zero_right htg (i - j - 1)
    calc s ^ i * g₀ * t ^ i * (s ^ j * g₀ * t ^ j)
        = s ^ i * (g₀ * (t ^ i * s ^ j) * g₀) * t ^ j := by noncomm_ring
      _ = s ^ i * (g₀ * t ^ (i - j) * g₀) * t ^ j := by rw [hsplit]
      _ = s ^ i * (g₀ * (t ^ (i - j) * g₀)) * t ^ j := by noncomm_ring
      _ = s ^ i * (g₀ * 0) * t ^ j := by rw [hz]
      _ = 0 := by simp

end ShiftedCopies

/-- **`n` pairwise orthogonal idempotents, each equivalent to `1`.**  Built
inside `1` itself, all at once, from `1`'s own infinite decomposition: no
splitting of a shrinking remainder is needed, since the shifted copies of the
complement are already pairwise orthogonal and each embedding is independent. -/
theorem exists_orthogonal_unit_family (hR : IsPurelyInfiniteSimpleRing R)
    (n : ℕ) :
    ∃ r : Fin n → R, (∀ i, IsIdempotentElem (r i)) ∧
      (∀ i j, i ≠ j → r i * r j = 0) ∧ ∀ i, IsEquivalentIdempotent R (r i) 1 := by
  obtain ⟨f₀, g₀, hf₀, hg₀, hf₀g₀, hg₀f₀, hsum₀, hequiv₀, hg₀ne⟩ :=
    isInfiniteIdempotent_one hR
  obtain ⟨s₀, t₀, hts₀, hst₀, hes₀, hse₀, het₀, hte₀⟩ :=
    exists_normalized_isometry IsIdempotentElem.one hf₀ (one_mul f₀) (mul_one f₀)
      hequiv₀
  have hf₀s₀ : f₀ * s₀ = s₀ := by
    calc f₀ * s₀ = s₀ * t₀ * s₀ := by rw [hst₀]
      _ = s₀ * (t₀ * s₀) := by noncomm_ring
      _ = s₀ * 1 := by rw [hts₀]
      _ = s₀ := hse₀
  have ht₀f₀ : t₀ * f₀ = t₀ := by
    calc t₀ * f₀ = t₀ * (s₀ * t₀) := by rw [hst₀]
      _ = t₀ * s₀ * t₀ := by noncomm_ring
      _ = 1 * t₀ := by rw [hts₀]
      _ = t₀ := het₀
  have hg₀s₀ : g₀ * s₀ = 0 := by
    have h1 : (1 : R) * s₀ = f₀ * s₀ + g₀ * s₀ := by rw [hsum₀, add_mul]
    rw [hes₀, hf₀s₀] at h1
    exact add_left_cancel (h1.symm.trans (add_zero s₀).symm)
  have ht₀g₀ : t₀ * g₀ = 0 := by
    have h1 : t₀ * (1 : R) = t₀ * f₀ + t₀ * g₀ := by rw [hsum₀, mul_add]
    rw [hte₀, ht₀f₀] at h1
    exact add_left_cancel (h1.symm.trans (add_zero t₀).symm)
  set g : ℕ → R := fun k => s₀ ^ k * g₀ * t₀ ^ k with hgdef
  have hgidem : ∀ k, IsIdempotentElem (g k) := fun k =>
    isIdempotentElem_shiftedCopy hts₀ hes₀ hg₀ k
  have hgne : ∀ k, g k ≠ 0 := fun k =>
    ne_zero_of_isEquivalentIdempotent hg₀ hg₀ne
      (isEquivalentIdempotent_shiftedCopy hts₀ hes₀ k).symm
  have hgortho : ∀ i j : ℕ, i ≠ j → g i * g j = 0 := fun i j hij =>
    shiftedCopy_orthogonal hts₀ hes₀ hg₀s₀ ht₀g₀ hij
  have hsand : ∀ a : R, a ≠ 0 → ∃ x y : R, x * a * y = 1 :=
    fun a ha => exists_sandwich_of_isPurelyInfiniteSimpleRing hR ha
  have hchoice : ∀ i : Fin n, ∃ f : R, IsIdempotentElem f ∧
      IdempotentLE f (g (i : ℕ)) ∧ IsEquivalentIdempotent R f 1 := fun i =>
    exists_idempotentLE_equivalent hsand (hgidem (i : ℕ)) IsIdempotentElem.one
      (hgne (i : ℕ))
  choose r hridem hrle hrequiv using hchoice
  refine ⟨r, hridem, fun i j hij => ?_, hrequiv⟩
  have h1 : r i * g (i : ℕ) = r i := (hrle i).2
  have h2 : g (j : ℕ) * r j = r j := (hrle j).1
  have hne' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  have h3 : r i * g (j : ℕ) = 0 := by
    calc r i * g (j : ℕ) = (r i * g (i : ℕ)) * g (j : ℕ) := by rw [h1]
      _ = r i * (g (i : ℕ) * g (j : ℕ)) := by noncomm_ring
      _ = r i * 0 := by rw [hgortho (i : ℕ) (j : ℕ) hne']
      _ = 0 := mul_zero _
  calc r i * r j = r i * (g (j : ℕ) * r j) := by rw [h2]
    _ = (r i * g (j : ℕ)) * r j := by noncomm_ring
    _ = 0 * r j := by rw [h3]
    _ = 0 := zero_mul _

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.exists_orthogonal_unit_family
