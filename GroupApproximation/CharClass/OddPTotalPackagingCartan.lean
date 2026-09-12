import GroupApproximation.CharClass.OddPTotalPackagingExpand

/-!
# Packaging the reduced powers, part 4: the Cartan formula on junk-free classes

For junk-free classes `c`, `c'` of even degrees `a`, `b`:

`P^i(c ⌣ c') = Σ_{j ≤ i} P^j c · P^{i−j} c'`.

The proof applies the degree projection onto `a + b + 2i(p − 1)` to the multiplicativity of the total
power, expands both factors over their graded pieces (`ptotOf_eq_sum`), and collapses the rectangle
of index pairs to the antidiagonal.  The normalising powers of `μ` cancel because
`(a + b)/2 − i = (a/2 − j) + (b/2 − (i − j))`.  The formula extends bilinearly to all junk-free
even classes (`totalP_cartan`).
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace OddPTotal

open CategoryTheory

noncomputable section

/-- Collapse a sum over a rectangle of index pairs to the antidiagonal `s + s' = i`. -/
theorem sum_rect_ite {M : Type*} [AddCommMonoid M] (A B i : ℕ) (F : ℕ → ℕ → M)
    (hA : ∀ s, A < s → ∀ s', F s s' = 0) (hB : ∀ s', B < s' → ∀ s, F s s' = 0) :
    ∑ s ∈ Finset.range (A + 1), ∑ s' ∈ Finset.range (B + 1), (if s + s' = i then F s s' else 0)
      = ∑ j ∈ Finset.range (i + 1), F j (i - j) := by
  have hinner : ∀ s, ∑ s' ∈ Finset.range (B + 1), (if s + s' = i then F s s' else 0)
      = if s ≤ i then F s (i - s) else 0 := by
    intro s
    by_cases hs : s ≤ i
    · rw [if_pos hs, Finset.sum_eq_single (i - s)]
      · rw [if_pos (by omega)]
      · intro s' _ hne
        rw [if_neg (by omega)]
      · intro hn
        rw [if_pos (by omega)]
        exact hB (i - s) (by rw [Finset.mem_range] at hn; omega) s
    · rw [if_neg hs]
      exact Finset.sum_eq_zero fun s' _ => if_neg (by omega)
  rw [Finset.sum_congr rfl fun s _ => hinner s]
  have hright : ∑ j ∈ Finset.range (i + 1), F j (i - j)
      = ∑ j ∈ Finset.range (i + 1), (if j ≤ i then F j (i - j) else 0) :=
    Finset.sum_congr rfl fun j hj => by rw [if_pos (by rw [Finset.mem_range] at hj; omega)]
  rw [hright, Finset.sum_subset (Finset.range_subset_range.mpr (by omega : A + 1 ≤ A + i + 1)),
    Finset.sum_subset (Finset.range_subset_range.mpr (by omega : i + 1 ≤ A + i + 1))]
  · intro j _ hj
    rw [Finset.mem_range] at hj
    rw [if_neg (by omega)]
  · intro s _ hs
    rw [Finset.mem_range] at hs
    by_cases hsi : s ≤ i
    · rw [if_pos hsi]
      exact hA s (by omega) (i - s)
    · rw [if_neg hsi]

namespace TotalReducedPowers

variable {p : ℕ} (R : TotalReducedPowers p)

/-- **The Cartan formula on junk-free homogeneous classes of even degree.** -/
theorem cartan_piece (X : TopCat.{0}) (hp : 2 ≤ p) {a b : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 0)
    (c : TotalPieceOf (ZMod p) X a) (c' : TotalPieceOf (ZMod p) X b)
    (hc : R.IsGoodPiece X a c) (hc' : R.IsGoodPiece X b c') (i : ℕ) :
    R.totalP X i (TotalHOf.of (ZMod p) X (a + b) (cup c c'))
      = ∑ j ∈ Finset.range (i + 1),
          R.totalP X j (TotalHOf.of (ZMod p) X a c)
            * R.totalP X (i - j) (TotalHOf.of (ZMod p) X b c') := by
  by_cases hi : 2 * i ≤ a + b
  · have hab : (a + b) % 2 = 0 := by omega
    rw [R.totalP_of_eq X hab i hi,
      R.ptot_mul X (Nat.even_iff.mpr ha) (Nat.even_iff.mpr hb) c c',
      R.ptotOf_eq_sum X hp ha c hc, R.ptotOf_eq_sum X hp hb c' hc', Finset.sum_mul_sum]
    have hproj : projDeg (ZMod p) X (a + b + 2 * i * (p - 1))
        (∑ s ∈ Finset.range (a / 2 + 1), ∑ s' ∈ Finset.range (b / 2 + 1),
          (R.μ ^ (a / 2 - s) • R.totalP X s (TotalHOf.of (ZMod p) X a c))
            * (R.μ ^ (b / 2 - s') • R.totalP X s' (TotalHOf.of (ZMod p) X b c')))
        = ∑ s ∈ Finset.range (a / 2 + 1), ∑ s' ∈ Finset.range (b / 2 + 1),
            (if s + s' = i then
              (R.μ ^ (a / 2 - s) * R.μ ^ (b / 2 - s')) •
                (R.totalP X s (TotalHOf.of (ZMod p) X a c)
                  * R.totalP X s' (TotalHOf.of (ZMod p) X b c'))
            else 0) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [smul_mul_left, mul_smul_right, smul_smul, projDeg_smul, R.projDeg_totalP_mul X hp,
        smul_ite, smul_zero]
    rw [hproj, sum_rect_ite (a / 2) (b / 2) i
      (fun s s' => (R.μ ^ (a / 2 - s) * R.μ ^ (b / 2 - s')) •
        (R.totalP X s (TotalHOf.of (ZMod p) X a c) * R.totalP X s' (TotalHOf.of (ZMod p) X b c')))
      (fun s hs s' => by
        beta_reduce
        rw [R.totalP_of_eq_zero X s (fun h => by have := h.2; omega), zero_mul, smul_zero])
      (fun s' hs' s => by
        beta_reduce
        rw [R.totalP_of_eq_zero X s' (fun h => by have := h.2; omega), mul_zero, smul_zero]),
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    by_cases hja : 2 * j ≤ a
    · by_cases hjb : 2 * (i - j) ≤ b
      · rw [smul_smul]
        have hK : (a + b) / 2 - i = (a / 2 - j) + (b / 2 - (i - j)) := by omega
        have hunit : R.μinv ^ ((a + b) / 2 - i) * (R.μ ^ (a / 2 - j) * R.μ ^ (b / 2 - (i - j)))
            = 1 := by
          rw [hK, pow_add]
          calc R.μinv ^ (a / 2 - j) * R.μinv ^ (b / 2 - (i - j))
                * (R.μ ^ (a / 2 - j) * R.μ ^ (b / 2 - (i - j)))
              = (R.μinv ^ (a / 2 - j) * R.μ ^ (a / 2 - j))
                  * (R.μinv ^ (b / 2 - (i - j)) * R.μ ^ (b / 2 - (i - j))) := by ring
            _ = 1 := by rw [R.μinv_pow_mul_pow, R.μinv_pow_mul_pow, one_mul]
        rw [hunit, one_smul]
      · rw [R.totalP_of_eq_zero X (i - j) (fun h => hjb h.2), mul_zero, smul_zero, smul_zero]
    · rw [R.totalP_of_eq_zero X j (fun h => hja h.2), zero_mul, smul_zero, smul_zero]
  · rw [R.totalP_of_eq_zero X i (fun h => hi h.2)]
    refine (Finset.sum_eq_zero fun j hj => ?_).symm
    rw [Finset.mem_range] at hj
    by_cases hja : 2 * j ≤ a
    · rw [R.totalP_of_eq_zero X (i - j) (fun h => by have := h.2; omega), mul_zero]
    · rw [R.totalP_of_eq_zero X j (fun h => hja h.2), zero_mul]

/-- **The Cartan formula on junk-free even classes.** -/
theorem totalP_cartan (X : TopCat.{0}) (hp : 2 ≤ p) {u v : TotalHOf (ZMod p) X}
    (hue : TotalHOf.IsEven u) (hve : TotalHOf.IsEven v) (hu : R.IsGood X u) (hv : R.IsGood X v)
    (i : ℕ) :
    R.totalP X i (u * v)
      = ∑ j ∈ Finset.range (i + 1), R.totalP X j u * R.totalP X (i - j) v := by
  classical
  have hsplit : ∀ a b : ℕ,
      R.totalP X i (TotalHOf.of (ZMod p) X a (u a) * TotalHOf.of (ZMod p) X b (v b))
        = ∑ j ∈ Finset.range (i + 1),
            R.totalP X j (TotalHOf.of (ZMod p) X a (u a))
              * R.totalP X (i - j) (TotalHOf.of (ZMod p) X b (v b)) := by
    intro a b
    by_cases ha : a % 2 = 0
    · by_cases hb : b % 2 = 0
      · rw [← TotalHOf.of_mul]
        exact R.cartan_piece X hp ha hb (u a) (v b) (hu a ha) (hv b hb) i
      · have hvb : v b = 0 := hve b (Nat.odd_iff.mpr (by omega))
        simp only [hvb, map_zero, mul_zero, Finset.sum_const_zero]
    · have hua : u a = 0 := hue a (Nat.odd_iff.mpr (by omega))
      simp only [hua, map_zero, zero_mul, Finset.sum_const_zero]
  calc R.totalP X i (u * v)
      = R.totalP X i ((∑ a ∈ DFinsupp.support u, TotalHOf.of (ZMod p) X a (u a))
          * ∑ b ∈ DFinsupp.support v, TotalHOf.of (ZMod p) X b (v b)) := by
        rw [TotalHOf.sum_support_of', TotalHOf.sum_support_of']
    _ = ∑ a ∈ DFinsupp.support u, ∑ b ∈ DFinsupp.support v, ∑ j ∈ Finset.range (i + 1),
          R.totalP X j (TotalHOf.of (ZMod p) X a (u a))
            * R.totalP X (i - j) (TotalHOf.of (ZMod p) X b (v b)) := by
        rw [Finset.sum_mul_sum, map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_sum]
        exact Finset.sum_congr rfl fun b _ => hsplit a b
    _ = ∑ j ∈ Finset.range (i + 1), R.totalP X j u * R.totalP X (i - j) v := by
        conv_rhs =>
          rw [← TotalHOf.sum_support_of' (ZMod p) X u, ← TotalHOf.sum_support_of' (ZMod p) X v]
        simp only [map_sum, Finset.sum_mul_sum]
        rw [Finset.sum_comm (s := Finset.range (i + 1))]
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_comm

end TotalReducedPowers

end

end OddPTotal

#audit_axioms OddPTotal.sum_rect_ite
#audit_axioms OddPTotal.TotalReducedPowers.cartan_piece
#audit_axioms OddPTotal.TotalReducedPowers.totalP_cartan

end CharClass
end GroupApproximation
