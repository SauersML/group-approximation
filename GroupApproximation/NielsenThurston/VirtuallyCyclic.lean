import GroupApproximation.GGT.WPDAcylindricalHyperbolicity
import Mathlib.GroupTheory.OrderOfElement

/-!
# Commuting with an element of a virtually cyclic group

McCarthy's theorem (J. D. McCarthy, *Normalizers and centralizers of pseudo-Anosov mapping
classes*, preprint 1982, Theorem 1; Chen–Salter, arXiv:1804.11235v1, Proposition 2.6) says
that the centralizer of a pseudo-Anosov mapping class is virtually cyclic. The genus-3 Birman
argument uses it in one form (review §3, Lemma A Step 3): if `ψ` commutes with the
pseudo-Anosov `φ`, then `ψ ^ j = φ ^ i` for some `j ≥ 1`.

This file proves that consequence for an arbitrary virtually cyclic group, using the repo's
`GroupApproximation.GGT.IsVirtuallyCyclic` (finitely many cosets of a cyclic subgroup cover
the group).

## Main results
* `exists_pow_eq_zpow_of_isVirtuallyCyclic`: in a virtually cyclic group, every element has a
  positive power that is a power of any given element of infinite order.
-/

namespace GroupApproximation
namespace NielsenThurston

/-- **Powers in a virtually cyclic group.** Let `G` be virtually cyclic and `φ ∈ G` of infinite
order. Then every `ψ ∈ G` has a positive power `ψ ^ j` equal to a power `φ ^ i`.

If `⟨g⟩` has finite index, then `ψ ^ a = g ^ s` and `φ ^ b = g ^ t` with `a, b ≥ 1`, and
`t ≠ 0` because `φ` has infinite order. So `ψ ^ (a t) = g ^ (s t) = φ ^ (b s)`. -/
theorem exists_pow_eq_zpow_of_isVirtuallyCyclic {G : Type*} [Group G]
    (hG : GGT.IsVirtuallyCyclic G) {φ : G} (hφ : ¬ IsOfFinOrder φ) (ψ : G) :
    ∃ j : ℕ, 0 < j ∧ ∃ i : ℤ, ψ ^ j = φ ^ i := by
  obtain ⟨g, hg⟩ := GGT.exists_zpow_eq_of_isVirtuallyCyclic hG
  obtain ⟨a, s, ha, hψ⟩ := hg ψ
  obtain ⟨b, t, hb, hφb⟩ := hg φ
  have ht : t ≠ 0 := by
    rintro rfl
    exact hφ (isOfFinOrder_iff_pow_eq_one.mpr ⟨b, hb, by simpa using hφb⟩)
  have hz : ψ ^ ((a : ℤ) * t) = φ ^ ((b : ℤ) * s) := by
    rw [zpow_mul, zpow_natCast, hψ, zpow_mul, zpow_natCast, hφb, ← zpow_mul, ← zpow_mul,
      mul_comm]
  obtain ⟨n, rfl | rfl⟩ := t.eq_nat_or_neg
  · refine ⟨a * n, Nat.mul_pos ha (by omega), (b : ℤ) * s, ?_⟩
    rw [← zpow_natCast, Nat.cast_mul]
    exact hz
  · refine ⟨a * n, Nat.mul_pos ha (by omega), -((b : ℤ) * s), ?_⟩
    rw [mul_neg, zpow_neg] at hz
    rw [zpow_neg, ← hz, inv_inv, ← zpow_natCast, Nat.cast_mul]

end NielsenThurston
end GroupApproximation
