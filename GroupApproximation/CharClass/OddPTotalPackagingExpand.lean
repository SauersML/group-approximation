import GroupApproximation.CharClass.OddPTotalPackagingGood

/-!
# Packaging the reduced powers, part 3: the expansion of a junk-free total power

For a junk-free class `c` of even degree `a`, the total power splits over its graded pieces:
`ptotOf a c = Σ_{s ≤ a/2} μ^{a/2 − s} • P^s c`.  The graded piece `P^s c` sits in degree
`a + 2s(p − 1)`, and the degree projection of a product of two pieces keeps exactly the pairs
whose indices add to the target index.  These are the inputs of the Cartan formula on junk-free
classes (`OddPTotalPackagingCartan.lean`).
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace OddPTotal

open CategoryTheory

noncomputable section

namespace TotalReducedPowers

variable {p : ℕ} (R : TotalReducedPowers p)

theorem totalP_of_eq (X : TopCat.{0}) {a : ℕ} (ha : a % 2 = 0) (s : ℕ) (hs : 2 * s ≤ a)
    (c : TotalPieceOf (ZMod p) X a) :
    R.totalP X s (TotalHOf.of (ZMod p) X a c)
      = R.μinv ^ (a / 2 - s) • projDeg (ZMod p) X (a + 2 * s * (p - 1)) (ptotOf R.D X a c) := by
  rw [R.totalP_of, R.pieceP_apply, if_pos ⟨ha, hs⟩]

theorem totalP_of_eq_zero (X : TopCat.{0}) {a : ℕ} (s : ℕ) (hs : ¬ (a % 2 = 0 ∧ 2 * s ≤ a))
    (c : TotalPieceOf (ZMod p) X a) : R.totalP X s (TotalHOf.of (ZMod p) X a c) = 0 := by
  rw [R.totalP_of, R.pieceP_apply, if_neg hs]

/-- `P^s` of a homogeneous class of degree `a` is concentrated in degree `a + 2s(p − 1)`. -/
theorem totalP_of_homogeneous (X : TopCat.{0}) (a s : ℕ) (c : TotalPieceOf (ZMod p) X a) :
    ∃ y : TotalPieceOf (ZMod p) X (a + 2 * s * (p - 1)),
      R.totalP X s (TotalHOf.of (ZMod p) X a c) = TotalHOf.of (ZMod p) X (a + 2 * s * (p - 1)) y := by
  by_cases h : a % 2 = 0 ∧ 2 * s ≤ a
  · refine ⟨R.μinv ^ (a / 2 - s) •
      TotalHOf.component (ZMod p) X (a + 2 * s * (p - 1)) (ptotOf R.D X a c), ?_⟩
    rw [R.totalP_of_eq X h.1 s h.2, projDeg_apply, of_smul]
  · exact ⟨0, by rw [R.totalP_of_eq_zero X s h, map_zero]⟩

/-- **The expansion of the total power of a junk-free class over its graded pieces.** -/
theorem ptotOf_eq_sum (X : TopCat.{0}) (hp : 2 ≤ p) {a : ℕ} (ha : a % 2 = 0)
    (c : TotalPieceOf (ZMod p) X a) (hc : R.IsGoodPiece X a c) :
    ptotOf R.D X a c = ∑ s ∈ Finset.range (a / 2 + 1),
      R.μ ^ (a / 2 - s) • R.totalP X s (TotalHOf.of (ZMod p) X a c) := by
  have hinj : ∀ s ∈ Finset.range (a / 2 + 1), ∀ s' ∈ Finset.range (a / 2 + 1),
      a + 2 * s * (p - 1) = a + 2 * s' * (p - 1) → s = s' :=
    fun _ _ _ _ h => goodDeg_inj hp h
  rw [eq_sum_components (ZMod p) X (ptotOf R.D X a c)
      ((Finset.range (a / 2 + 1)).image fun s => a + 2 * s * (p - 1)) ?_, Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_range] at hs
    rw [R.totalP_of_eq X ha s (by omega), smul_smul, ← mul_pow, mul_comm R.μ, R.μinv_mul,
      one_pow, one_smul, projDeg_apply]
  · intro e he
    by_cases hle : e ≤ p * a
    · by_cases hev : e % 2 = 0
      · by_cases hg : GoodDeg p a e
        · obtain ⟨s, hs, rfl⟩ := exists_of_goodDeg hp hle hg
          exact absurd (Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr (by omega), rfl⟩) he
        · exact hc e hev hg
      · exact R.component_ptotOf_of_odd X ha e c (by omega)
    · exact R.component_ptotOf_of_lt X a e c (by omega)

/-- **The degree projection of a product of two graded pieces** keeps the pair exactly when the
indices add up to the target index. -/
theorem projDeg_totalP_mul (X : TopCat.{0}) (hp : 2 ≤ p) (a b s s' i : ℕ)
    (c : TotalPieceOf (ZMod p) X a) (c' : TotalPieceOf (ZMod p) X b) :
    projDeg (ZMod p) X (a + b + 2 * i * (p - 1))
        (R.totalP X s (TotalHOf.of (ZMod p) X a c) * R.totalP X s' (TotalHOf.of (ZMod p) X b c'))
      = if s + s' = i then
          R.totalP X s (TotalHOf.of (ZMod p) X a c) * R.totalP X s' (TotalHOf.of (ZMod p) X b c')
        else 0 := by
  obtain ⟨y, hy⟩ := R.totalP_of_homogeneous X a s c
  obtain ⟨y', hy'⟩ := R.totalP_of_homogeneous X b s' c'
  rw [hy, hy', ← TotalHOf.of_mul, projDeg_of]
  by_cases h : s + s' = i
  · rw [if_pos h, if_pos]
    subst h
    ring
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    have h'' : a + b + 2 * (s + s') * (p - 1) = a + b + 2 * i * (p - 1) :=
      calc a + b + 2 * (s + s') * (p - 1)
          = a + 2 * s * (p - 1) + (b + 2 * s' * (p - 1)) := by ring
        _ = a + b + 2 * i * (p - 1) := h'
    exact goodDeg_inj hp h''

end TotalReducedPowers

end

end OddPTotal

#audit_axioms OddPTotal.TotalReducedPowers.totalP_of_homogeneous
#audit_axioms OddPTotal.TotalReducedPowers.ptotOf_eq_sum
#audit_axioms OddPTotal.TotalReducedPowers.projDeg_totalP_mul

end CharClass
end GroupApproximation
