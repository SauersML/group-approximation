import GroupApproximation.Pestov91.Toeplitz
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Separation.Profinite

/-!
# The Toeplitz subshift

`X` is the set of sequences `ℤ → Bool` all of whose finite windows occur in `toeplitz`. It is a
closed shift-invariant subset of the full shift, so it is compact, Hausdorff and totally
disconnected. The shift acts freely and minimally, so `X` is infinite.
-/

namespace GroupApproximation.Pestov91

/-- Sequences all of whose finite windows occur in `toeplitz`. -/
def subshiftCarrier : Set (ℤ → Bool) :=
  {y | ∀ (a : ℤ) (L : ℕ), ∃ b : ℤ, ∀ i : ℕ, i < L → y (a + i) = toeplitz (b + i)}

theorem isClosed_subshiftCarrier : IsClosed subshiftCarrier := by
  have hw : ∀ (a : ℤ) (L : ℕ), IsClosed
      {y : ℤ → Bool | ∃ b : ℤ, ∀ i : ℕ, i < L → y (a + i) = toeplitz (b + i)} := by
    intro a L
    have hc : Continuous fun (y : ℤ → Bool) (i : Fin L) => y (a + (i : ℕ)) :=
      continuous_pi fun i => continuous_apply (a + ((i : ℕ) : ℤ))
    have := (isClosed_discrete
      {v : Fin L → Bool | ∃ b : ℤ, ∀ i : Fin L, v i = toeplitz (b + (i : ℕ))}).preimage hc
    convert this using 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b, fun i => hb i i.2⟩
    · rintro ⟨b, hb⟩
      exact ⟨b, fun i hi => hb ⟨i, hi⟩⟩
  have e : subshiftCarrier = ⋂ (a : ℤ) (L : ℕ),
      {y : ℤ → Bool | ∃ b : ℤ, ∀ i : ℕ, i < L → y (a + i) = toeplitz (b + i)} := by
    ext y
    simp only [subshiftCarrier, Set.mem_setOf_eq, Set.mem_iInter]
  rw [e]
  exact isClosed_iInter fun a => isClosed_iInter fun L => hw a L

theorem subshiftCarrier_translate_mem (m : ℤ) {x : ℤ → Bool} (hx : x ∈ subshiftCarrier) :
    (fun i => x (i + m)) ∈ subshiftCarrier := by
  simp only [subshiftCarrier, Set.mem_setOf_eq] at hx ⊢
  intro a L
  obtain ⟨b, hb⟩ := hx (a + m) L
  refine ⟨b, fun i hi => ?_⟩
  rw [show a + (i : ℤ) + m = a + m + i by ring]
  exact hb i hi

/-- The Toeplitz subshift. -/
abbrev X : Type := ↥subshiftCarrier

instance : CompactSpace X :=
  isCompact_iff_compactSpace.mp isClosed_subshiftCarrier.isCompact

instance : T2Space X := inferInstance

instance : TotallyDisconnectedSpace X := inferInstance

theorem mem_window (y : X) (a : ℤ) (L : ℕ) :
    ∃ b : ℤ, ∀ i : ℕ, i < L → y.1 (a + i) = toeplitz (b + i) := by
  have h := y.2
  simp only [subshiftCarrier, Set.mem_setOf_eq] at h
  exact h a L

/-- The point `toeplitz` of `X`. -/
def toeplitzPoint : X :=
  ⟨toeplitz, by
    simp only [subshiftCarrier, Set.mem_setOf_eq]
    exact fun a _ => ⟨a, fun _ _ => rfl⟩⟩

theorem shift_mem (n : ℤ) (y : X) : (fun k => y.1 (n + k)) ∈ subshiftCarrier := by
  have e : (fun k => y.1 (n + k)) = fun i => y.1 (i + n) := funext fun k => by rw [add_comm]
  rw [e]
  exact subshiftCarrier_translate_mem n y.2

/-- The shift by `n` on points of `X`. -/
def shiftMap (n : ℤ) (y : X) : X := ⟨fun k => y.1 (n + k), shift_mem n y⟩

theorem continuous_shiftMap (n : ℤ) : Continuous (shiftMap n) :=
  (show Continuous fun y : X => fun k => y.1 (n + k) from
    continuous_pi fun k => (continuous_apply (n + k)).comp continuous_subtype_val).subtype_mk
      fun y => shift_mem n y

theorem shiftMap_add (m n : ℤ) (y : X) : shiftMap (m + n) y = shiftMap m (shiftMap n y) :=
  Subtype.ext <| funext fun k => by
    show y.1 (m + n + k) = y.1 (n + (m + k))
    rw [show m + n + k = n + (m + k) by ring]

theorem shiftMap_zero (y : X) : shiftMap 0 y = y :=
  Subtype.ext <| funext fun k => by
    show y.1 (0 + k) = y.1 k
    rw [zero_add]

/-- The shift homeomorphism: `(shiftBy n y) k = y (n + k)`. -/
def shiftBy (n : ℤ) : X ≃ₜ X where
  toFun := shiftMap n
  invFun := shiftMap (-n)
  left_inv y := by rw [← shiftMap_add, neg_add_cancel, shiftMap_zero]
  right_inv y := by rw [← shiftMap_add, add_neg_cancel, shiftMap_zero]
  continuous_toFun := continuous_shiftMap n
  continuous_invFun := continuous_shiftMap (-n)

@[simp] theorem shiftBy_apply (n : ℤ) (y : X) (k : ℤ) : (shiftBy n y).1 k = y.1 (n + k) := rfl

theorem shiftBy_apply' (n : ℤ) (y : X) (k : ℤ) : (shiftBy n y).1 k = y.1 (k + n) := by
  rw [shiftBy_apply, add_comm]

theorem shiftBy_add (m n : ℤ) (y : X) : shiftBy (m + n) y = shiftBy m (shiftBy n y) :=
  shiftMap_add m n y

theorem shiftBy_zero (y : X) : shiftBy 0 y = y := shiftMap_zero y

theorem shiftBy_symm (n : ℤ) : (shiftBy n).symm = shiftBy (-n) := Homeomorph.ext fun _ => rfl

/-- The left shift `T`, `(T y) k = y (1 + k)`. -/
def shiftHomeo : X ≃ₜ X := shiftBy 1

theorem shiftBy_natCast (n : ℕ) : shiftBy n = shiftHomeo ^ n := by
  induction n with
  | zero =>
    refine Homeomorph.ext fun y => ?_
    rw [Nat.cast_zero, pow_zero, Homeomorph.one_apply, shiftBy_zero]
  | succ n ih =>
    refine Homeomorph.ext fun y => ?_
    rw [Nat.cast_succ, pow_succ, Homeomorph.mul_apply, shiftBy_add, ← ih, shiftHomeo]

theorem shiftBy_eq_zpow (n : ℤ) : shiftBy n = shiftHomeo ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast, shiftBy_natCast]
  · refine Homeomorph.ext fun y => ?_
    rw [zpow_neg, zpow_natCast, Homeomorph.inv_apply, ← shiftBy_natCast, shiftBy_symm]

/-- Uniform recurrence for points of `X`. -/
theorem exists_return (b : ℤ) (L : ℕ) :
    ∃ K : ℕ, ∀ (y : X) (a : ℤ), ∃ r : ℕ, r < 2 ^ K ∧
      ∀ i : ℕ, i < L → y.1 (a + r + i) = toeplitz (b + i) := by
  obtain ⟨K, hK⟩ := toeplitz_uniformly_recurrent b L
  refine ⟨K, fun y a => ?_⟩
  obtain ⟨c, hc⟩ := mem_window y a (2 ^ K + L)
  obtain ⟨r, hr, hr'⟩ := hK c
  refine ⟨r, hr, fun i hi => ?_⟩
  have h1 := hc (r + i) (by omega)
  simp only [Nat.cast_add, ← add_assoc] at h1
  rw [h1, hr' i hi]

theorem shiftBy_ne_self (y : X) {n : ℤ} (hn : n ≠ 0) : shiftBy n y ≠ y := by
  intro hy
  have hper : ∀ k : ℤ, y.1 (n + k) = y.1 k := fun k => by
    rw [← shiftBy_apply, hy]
  obtain ⟨p, hp, hper'⟩ : ∃ p : ℕ, 0 < p ∧ ∀ k : ℤ, y.1 (k + p) = y.1 k := by
    by_cases hpos : 0 < n
    · refine ⟨n.toNat, by omega, fun k => ?_⟩
      rw [Int.toNat_of_nonneg hpos.le, add_comm]
      exact hper k
    · refine ⟨(-n).toNat, by omega, fun k => ?_⟩
      rw [Int.toNat_of_nonneg (by omega)]
      have := hper (k + -n)
      rw [show n + (k + -n) = k by ring] at this
      exact this.symm
  obtain ⟨h, hh⟩ := toeplitz_exists_ne_of_pos hp
  obtain ⟨K, hK⟩ := exists_return h (p + 1)
  obtain ⟨r, -, hr⟩ := hK y 0
  have e1 := hr 0 (by omega)
  have e2 := hr p (by omega)
  simp only [Nat.cast_zero, add_zero, zero_add] at e1 e2
  rw [hper'] at e2
  exact hh (e2.symm.trans e1)

theorem shiftBy_injective_orbit (y : X) : Function.Injective fun n : ℤ => shiftBy n y := by
  intro m n hmn
  by_contra hne
  apply shiftBy_ne_self y (sub_ne_zero.mpr hne)
  have := congrArg (shiftBy (-n)) hmn
  simp only [← shiftBy_add] at this
  rw [show m - n = -n + m by ring, this, neg_add_cancel, shiftBy_zero]

instance : Infinite X := Infinite.of_injective _ (shiftBy_injective_orbit toeplitzPoint)

theorem zpow_shiftHomeo_ne_self : ∀ j : ℤ, j ≠ 0 → ∀ x : X, (shiftHomeo ^ j) x ≠ x := by
  intro j hj x
  rw [← shiftBy_eq_zpow]
  exact shiftBy_ne_self x hj

end GroupApproximation.Pestov91
