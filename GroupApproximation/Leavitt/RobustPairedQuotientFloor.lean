import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Prod

/-!
# The robust paired-quotient floor after permutation repair

The exact paired-quotient obstruction has a quantitative finite counterpart.
Once the two diagonal transports have been repaired to permutations, changing
the left transport on `dV` labels and the right transport on `dW` labels can
change at most

`|W| * dV + |V| * dW`

entries of the crossed pairing table.  For a perfect binary pairing the
permuted table has `N * (N - 1) / 2` one-entries.  Combining this table bound
with the collision-repair estimates

`N * dV <= 4 * e00` and `N * dW <= 4 * e11`

gives the integer form

`N * (N - 1) <= 2 * e01 + 8 * e00 + 8 * e11`.

After division by `2*N^2`, this is exactly

`eps01 + 4*eps00 + 4*eps11 >= (N-1)/(2*N)`.

This file deliberately takes the two collision-repair bounds as hypotheses.
Their derivation from diagonal pairing mismatch is the remaining part of the
full robust theorem; it is not silently folded into the arithmetic endpoint.
-/

namespace GroupApproximation
namespace RobustPairedQuotient

variable {V W : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]

/-- The one-entries of a pairing table after applying maps to its two labels. -/
def oneSet (pair : V → W → Prop) [DecidableRel pair]
    (R : V → V) (L : W → W) : Finset (V × W) :=
  (Finset.univ.product Finset.univ).filter fun p ↦ pair (R p.1) (L p.2)

/-- The labels on which two maps disagree. -/
def disagreementSet {X : Type*} [Fintype X] [DecidableEq X]
    (f g : X → X) : Finset X :=
  Finset.univ.filter fun x ↦ f x ≠ g x

/-- Pairs whose left or right label map differs from a proposed repair. -/
def changedPairs (R Rbar : V → V) (L Lbar : W → W) : Finset (V × W) :=
  (disagreementSet R Rbar).product Finset.univ ∪
    Finset.univ.product (disagreementSet L Lbar)

theorem oneSet_subset_oneSet_union_changedPairs
    (pair : V → W → Prop) [DecidableRel pair]
    (R Rbar : V → V) (L Lbar : W → W) :
    oneSet pair Rbar Lbar ⊆ oneSet pair R L ∪ changedPairs R Rbar L Lbar := by
  intro p hp
  by_cases hR : R p.1 = Rbar p.1
  · by_cases hL : L p.2 = Lbar p.2
    · apply Finset.mem_union_left
      simpa [oneSet, hR, hL] using hp
    · apply Finset.mem_union_right
      simp [changedPairs, disagreementSet, hL]
  · apply Finset.mem_union_right
    simp [changedPairs, disagreementSet, hR]

/-- A row repair on `dV` labels and a column repair on `dW` labels changes at
most `|W|*dV + |V|*dW` entries of the pairing table. -/
theorem card_oneSet_repaired_le
    (pair : V → W → Prop) [DecidableRel pair]
    (R Rbar : V → V) (L Lbar : W → W) :
    (oneSet pair Rbar Lbar).card ≤
      (oneSet pair R L).card +
        (disagreementSet R Rbar).card * Fintype.card W +
          Fintype.card V * (disagreementSet L Lbar).card := by
  calc
    (oneSet pair Rbar Lbar).card ≤
        (oneSet pair R L ∪ changedPairs R Rbar L Lbar).card :=
      Finset.card_le_card
        (oneSet_subset_oneSet_union_changedPairs pair R Rbar L Lbar)
    _ ≤ (oneSet pair R L).card + (changedPairs R Rbar L Lbar).card :=
      Finset.card_union_le _ _
    _ ≤ (oneSet pair R L).card +
        ((disagreementSet R Rbar).product (Finset.univ : Finset W)).card +
          ((Finset.univ : Finset V).product (disagreementSet L Lbar)).card := by
      simpa [changedPairs, Nat.add_assoc] using
        Nat.add_le_add_left
          (Finset.card_union_le
            ((disagreementSet R Rbar).product (Finset.univ : Finset W))
            ((Finset.univ : Finset V).product (disagreementSet L Lbar)))
          (oneSet pair R L).card
    _ = (oneSet pair R L).card +
        (disagreementSet R Rbar).card * Fintype.card W +
          Fintype.card V * (disagreementSet L Lbar).card := by
      simp

/-- Integer form of the robust Hamming floor.

`e01` is the crossed-table one count, while `e00,e11` are the two diagonal
mismatch counts.  The hypotheses `hR,hL` are exactly the output required from
the collision-repair lemma. -/
theorem robust_floor_of_permutation_repairs
    (pair : V → W → Prop) [DecidableRel pair]
    (R₀ Rbar₀ : V → V) (L₁ Lbar₁ : W → W)
    (N e₀₀ e₁₁ : ℕ)
    (hV : Fintype.card V = N) (hW : Fintype.card W = N)
    (hperfectCount :
      2 * (oneSet pair Rbar₀ Lbar₁).card = N * (N - 1))
    (hR : N * (disagreementSet R₀ Rbar₀).card ≤ 4 * e₀₀)
    (hL : N * (disagreementSet L₁ Lbar₁).card ≤ 4 * e₁₁) :
    N * (N - 1) ≤
      2 * (oneSet pair R₀ L₁).card + 8 * e₀₀ + 8 * e₁₁ := by
  have htable := card_oneSet_repaired_le pair R₀ Rbar₀ L₁ Lbar₁
  rw [hV, hW] at htable
  calc
    N * (N - 1) = 2 * (oneSet pair Rbar₀ Lbar₁).card :=
      hperfectCount.symm
    _ ≤ 2 * ((oneSet pair R₀ L₁).card +
        (disagreementSet R₀ Rbar₀).card * N +
          N * (disagreementSet L₁ Lbar₁).card) :=
      Nat.mul_le_mul_left 2 htable
    _ = 2 * (oneSet pair R₀ L₁).card +
        2 * (N * (disagreementSet R₀ Rbar₀).card) +
          2 * (N * (disagreementSet L₁ Lbar₁).card) := by
      simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    _ ≤ 2 * (oneSet pair R₀ L₁).card +
        2 * (4 * e₀₀) + 2 * (4 * e₁₁) := by
      exact Nat.add_le_add
        (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hR) _)
        (Nat.mul_le_mul_left 2 hL)
    _ = 2 * (oneSet pair R₀ L₁).card + 8 * e₀₀ + 8 * e₁₁ := by
      simp [Nat.mul_assoc]

end RobustPairedQuotient
end GroupApproximation
