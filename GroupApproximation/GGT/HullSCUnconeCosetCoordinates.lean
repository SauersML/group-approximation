import GroupApproximation.GGT.HullSCUnconeExpansion
import GroupApproximation.GGT.HyperbolicFreeGroupAH
import GroupApproximation.Meta.AxiomGuard

/-!
# Un-coning cyclic peripherals, step 6: coordinates along a coset line

A coset `q⟨gᵢ⟩` of an infinite cyclic member is a line: its points are `q gᵢᵗ`, `t ∈ ℤ`, and in the
un-coned metric two of them are at most the difference of their coordinates apart
(`wordDist_mul_zpow_le`).  A `d̂`-bound between two of its points bounds that difference
(`natAbs_sub_le_of_mem_relBall`), since only finitely many exponents occur in a relative ball.

The expansions of the components of a triangle lying on one coset are intervals of this line whose
ends are chained by the connectors of `GGT/HullSCUnconeTriangleConnectors.lean`.  The two integer
lemmas below say that such a chain covers the interval it spans, up to the chaining constant.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u v w

namespace Uncone

section Line

variable {Q : Type u} [Group Q] {Lambda : Type w} {I : Type v}

/-- **Along a coset line the un-coned distance is at most the difference of coordinates.** -/
theorem wordDist_mul_zpow_le (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) (i : I) (q : Q) (a b : ℤ) :
    wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
      (q * g i ^ a) (q * g i ^ b) ≤ (b - a).natAbs := by
  have hS := (removeCyclicPeripherals J g hg hbaseInv).alphabet.symmetricGenerating
  have hgi : g i ∈ (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier :=
    Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨i, Or.inl rfl⟩))
  have h : (q * g i ^ a)⁻¹ * (q * g i ^ b) = g i ^ (b - a) := by
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left, ← zpow_neg, ← zpow_add, neg_add_eq_sub]
  unfold wordDist
  rw [h]
  exact wordNorm_zpow_le hS hgi (b - a)

/-- **A relative-ball bound between two points of a coset line bounds their coordinate
difference.** -/
theorem natAbs_sub_le_of_mem_relBall (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hinf : ∀ i : I, ¬ IsOfFinOrder (g i)) {T n : ℕ}
    (hT : ∀ (i : I) (e : Q), e ∈ J.relBall (Sum.inr i) n → (expo g i e).natAbs ≤ T)
    (i : I) (q : Q) (a b : ℤ)
    (h : (q * g i ^ a)⁻¹ * (q * g i ^ b) ∈ J.relBall (Sum.inr i) n) :
    (b - a).natAbs ≤ T := by
  have hv : (q * g i ^ a)⁻¹ * (q * g i ^ b) = g i ^ (b - a) := by
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left, ← zpow_neg, ← zpow_add, neg_add_eq_sub]
  have hb := hT i _ h
  rwa [hv, expo_zpow g i (hinf i)] at hb

end Line

/-! ## Chains of intervals on a line -/

/-- **One interval chained to both ends covers.**  If the interval from `a` to `a + m'` starts
within `T` of `0` and ends within `T` of `m`, every point between `0` and `m` is within `T` of it. -/
theorem cover_chain_one (T : ℕ) (a m' m t : ℤ) (h1 : a.natAbs ≤ T)
    (h2 : (a + m' - m).natAbs ≤ T) (ht1 : min 0 m ≤ t) (ht2 : t ≤ max 0 m) :
    ∃ s : ℤ, min 0 m' ≤ s ∧ s ≤ max 0 m' ∧ (t - (a + s)).natAbs ≤ T :=
  ⟨max (min 0 m') (min (t - a) (max 0 m')), by omega, by omega, by omega⟩

/-- **Two intervals chained end to end cover.**  If the first interval starts within `T` of `0`, the
second starts within `T` of the end of the first, and the second ends within `T` of `m`, every point
between `0` and `m` is within `T` of one of them. -/
theorem cover_chain_two (T : ℕ) (a₂ m₂ a₃ m₃ m t : ℤ) (h1 : a₂.natAbs ≤ T)
    (h2 : (a₃ - (a₂ + m₂)).natAbs ≤ T) (h3 : (a₃ + m₃ - m).natAbs ≤ T)
    (ht1 : min 0 m ≤ t) (ht2 : t ≤ max 0 m) :
    (∃ s : ℤ, min 0 m₂ ≤ s ∧ s ≤ max 0 m₂ ∧ (t - (a₂ + s)).natAbs ≤ T) ∨
      (∃ s : ℤ, min 0 m₃ ≤ s ∧ s ≤ max 0 m₃ ∧ (t - (a₃ + s)).natAbs ≤ T) := by
  by_cases hA : (t - (a₂ + max (min 0 m₂) (min (t - a₂) (max 0 m₂)))).natAbs ≤ T
  · exact Or.inl ⟨max (min 0 m₂) (min (t - a₂) (max 0 m₂)), by omega, by omega, hA⟩
  · refine Or.inr ⟨max (min 0 m₃) (min (t - a₃) (max 0 m₃)), by omega, by omega, ?_⟩
    omega

end Uncone

end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.Uncone.wordDist_mul_zpow_le
#audit_axioms GroupApproximation.GGT.Uncone.natAbs_sub_le_of_mem_relBall
#audit_axioms GroupApproximation.GGT.Uncone.cover_chain_one
#audit_axioms GroupApproximation.GGT.Uncone.cover_chain_two
