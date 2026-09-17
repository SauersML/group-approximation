import GroupApproximation.Manuscript.NonMF.Full.ClopenShrink.Shrink
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Sharpness: wandering does not shrink from a compact set to a clopen neighbourhood

`ClopenShrink.Shrink` proves the compact-to-clopen shrink for every finite window of
disjointness conditions.  The full printed notion `Dynamics.IsWandering` (all integer translates
pairwise disjoint) does not shrink.  The counterexample is the odometer `x ↦ x + 1` on the
2-adic integers, a compact metric totally disconnected space: the point `{0}` is wandering, since
`x + d = x` forces `d = 0`, but `2^k → 0`, so every neighbourhood `K` of `0` contains some
`n = 2^k ≠ 0`, which lies in both `K` and `T^n K`.

* `isWandering_zero`: `{0}` is wandering;
* `not_isWandering_of_mem_nhds`: no neighbourhood of `0` is wandering;
* `not_clopenWanderingShrinkStatement`: the literal shrink "a compact wandering `C` lies in a
  clopen wandering `K`" is false in compact metric totally disconnected spaces.

The point `0` is chain recurrent (the odometer is minimal), so this does not contradict the printed
sentence at tex 1489–1491, which only concerns compact subsets of `U = X ∖ CR(T)`.  The argument
there uses the clopen neighbourhood with a finite wandering clopen cover
(`exists_isClopen_wanderingCover_nhds_of_isCompact`), not a single wandering clopen set.
-/

namespace GroupApproximation.Full.NM11

open GroupApproximation.Dynamics (IsWandering)

/-- The 2-adic odometer `x ↦ x + 1`. -/
def odometer : ℤ_[2] ≃ₜ ℤ_[2] :=
  Homeomorph.addRight 1

theorem odometer_apply (x : ℤ_[2]) : odometer x = x + 1 :=
  rfl

theorem odometer_pow_apply (n : ℕ) (x : ℤ_[2]) : (odometer ^ n) x = x + n := by
  induction n with
  | zero => rw [pow_zero, Homeomorph.one_apply, Nat.cast_zero, add_zero]
  | succ n ih =>
    rw [pow_succ', Homeomorph.mul_apply, ih, odometer_apply, Nat.cast_succ, add_assoc]

/-- An integer power of the odometer fixing `0` is trivial. -/
theorem eq_zero_of_odometer_zpow_apply_zero {d : ℤ} (h : (odometer ^ d) 0 = 0) : d = 0 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · rw [zpow_natCast, odometer_pow_apply, zero_add, Nat.cast_eq_zero] at h
    omega
  · have h2 : (odometer ^ (n : ℤ)) ((odometer ^ (-(n : ℤ))) 0) = (odometer ^ (n : ℤ)) 0 := by
      rw [h]
    rw [GroupApproximation.Dynamics.zpow_apply_zpow_apply, add_neg_cancel, zpow_zero,
      Homeomorph.one_apply, zpow_natCast, odometer_pow_apply, zero_add, eq_comm,
      Nat.cast_eq_zero] at h2
    omega

/-- `{0}` is wandering for the odometer. -/
theorem isWandering_zero : IsWandering odometer.toEquiv {0} := by
  intro m n hmn
  show Disjoint (⇑(odometer.toEquiv ^ m) '' {0}) (⇑(odometer.toEquiv ^ n) '' {0})
  rw [image_toEquiv_zpow, image_toEquiv_zpow, Set.image_singleton, Set.image_singleton,
    Set.disjoint_singleton]
  intro h
  have hd := eq_zero_of_odometer_zpow_apply_zero
    (GroupApproximation.Dynamics.zpow_sub_apply_of_eq odometer h)
  exact hmn (by omega)

/-- Every neighbourhood of `0` contains a nonzero natural number (a power of `2`). -/
theorem exists_natCast_mem_of_mem_nhds {U : Set ℤ_[2]} (hU : U ∈ nhds (0 : ℤ_[2])) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : ℤ_[2]) ∈ U := by
  have hq : ‖((2 : ℕ) : ℤ_[2])‖ < 1 := by
    rw [PadicInt.norm_p]
    norm_num
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).eventually_mem hU).exists
  refine ⟨2 ^ k, pow_ne_zero k two_ne_zero, ?_⟩
  rw [Nat.cast_pow]
  exact hk

/-- **No neighbourhood of `0` is wandering** for the odometer: `0` is recurrent. -/
theorem not_isWandering_of_mem_nhds {K : Set ℤ_[2]} (hK : K ∈ nhds (0 : ℤ_[2])) :
    ¬ IsWandering odometer.toEquiv K := by
  intro hW
  obtain ⟨n, hn, hnK⟩ := exists_natCast_mem_of_mem_nhds hK
  have hne : (0 : ℤ) ≠ (n : ℤ) := by omega
  have hd : Disjoint (⇑(odometer.toEquiv ^ (0 : ℤ)) '' K) (⇑(odometer.toEquiv ^ (n : ℤ)) '' K) :=
    hW hne
  rw [image_toEquiv_zpow, image_toEquiv_zpow] at hd
  have h1 : (n : ℤ_[2]) ∈ ⇑(odometer ^ (0 : ℤ)) '' K :=
    ⟨n, hnK, by rw [zpow_zero, Homeomorph.one_apply]⟩
  have h2 : (n : ℤ_[2]) ∈ ⇑(odometer ^ (n : ℤ)) '' K :=
    ⟨0, mem_of_mem_nhds hK, by rw [zpow_natCast, odometer_pow_apply, zero_add]⟩
  exact Set.disjoint_left.1 hd h1 h2

/-- The literal compact-to-clopen shrink of the printed wandering property. -/
def ClopenWanderingShrinkStatement : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (C : Set X), IsCompact C → IsWandering T.toEquiv C →
    ∃ K : Set X, IsClopen K ∧ C ⊆ K ∧ IsWandering T.toEquiv K

/-- **The literal shrink is false**: the odometer on `ℤ_[2]` with `C = {0}`. -/
theorem not_clopenWanderingShrinkStatement : ¬ ClopenWanderingShrinkStatement := by
  intro h
  obtain ⟨K, hK, hCK, hW⟩ := h ℤ_[2] odometer {0} isCompact_singleton isWandering_zero
  exact not_isWandering_of_mem_nhds (hK.isOpen.mem_nhds (hCK (Set.mem_singleton 0))) hW

end GroupApproximation.Full.NM11

#audit_axioms GroupApproximation.Full.NM11.isWandering_zero
#audit_axioms GroupApproximation.Full.NM11.not_isWandering_of_mem_nhds
#audit_closed_axioms GroupApproximation.Full.NM11.not_clopenWanderingShrinkStatement
