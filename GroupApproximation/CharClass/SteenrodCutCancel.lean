import GroupApproximation.CharClass.SteenrodCut

/-!
# The cancellation behind the cup-`i` coboundary formula

This file contains the entire mathematical content of Steenrod's coboundary
formula

```text
δ(α ⌣ᵢ β) = δα ⌣ᵢ β + α ⌣ᵢ δβ + α ⌣ᵢ₋₁ β + β ⌣ᵢ₋₁ α        (mod 2)
```

as **one identity about cuts, valued in an arbitrary abelian group of exponent
two** (`cut_insert_cancel`).  No cochain, no simplex and no topology appears
here; the cochain formula in `SteenrodCoboundary.lean` and any chain-level
packaging of Steenrod's diagonal are two instances of the same lemma.

## The shape of the cancellation

Write `Θ A B` for the value attached to a pair of faces.  Deleting a vertex of
the ambient simplex and then cutting is the same as cutting and then deleting
(`cutU_map_succAbove`), so the coboundary of `α ⌣ᵢ₊₁ β` and the two terms
`δα ⌣ᵢ₊₁ β`, `α ⌣ᵢ₊₁ δβ` differ, mod 2, exactly by the terms in which the
deleted vertex **is** a cut point.  Those are

```text
∑_{|T| = i+2} ∑_{c ∈ T} ( Θ (cutU T \ c) (cutV T) + Θ (cutU T) (cutV T \ c) ),
```

and reindexing `T = insert c S` turns it into a sum over cut sets `S` of size
`i+1`, which is what `cut_insert_cancel` evaluates.

## Why it telescopes

For a threshold `t` put

```text
cutLow  S t = (cutU S ∩ {x < t}) ∪ (cutV S ∩ {x ≥ t})
cutHigh S t = (cutV S ∩ {x < t}) ∪ (cutU S ∩ {x ≥ t}),
```

the pair that follows the `α`-pattern strictly below `t` and the `β`-pattern
from `t` on.  Adding one new cut point `c` to `S` produces exactly the two
pairs at thresholds `c` and `c+1` -- in one order or the other according to
which side `c` was on, which is why the *sum* of the two terms is
`Ξ c + Ξ (c+1)` with `Ξ t = Θ (cutLow S t) (cutHigh S t)` in both cases.
Crossing an old cut point changes nothing (`cutLow_succ_of_mem`), so the sum
over `c ∉ S` extends to a sum over all `c` and telescopes to `Ξ 0 + Ξ N`.
Finally `Ξ 0 = Θ (cutV S) (cutU S)` and `Ξ N = Θ (cutU S) (cutV S)`: the two
surviving terms are the two orders of the `(i)`-cut, which is the pair
`α ⌣ᵢ₋₁ β + β ⌣ᵢ₋₁ α`.

There is deliberately **no involution**: an involution on the index set exists
but has to be described through the enumeration of the complement of `S`,
while the telescoping never mentions it.
-/

open CategoryTheory AlgebraicTopology Simplicial SimplexCategory

namespace GroupApproximation
namespace CharClass

variable {N : ℕ}

/-! ## 1. Inserting one cut point -/

theorem cutRank_insert_of_le {S : Finset (Fin N)} {c x : Fin N} (hc : c ∉ S) (hx : x ≤ c) :
    cutRank (insert c S) x = cutRank S x := by
  unfold cutRank
  congr 1
  rw [Finset.filter_insert, if_neg]
  intro hlt
  exact absurd (lt_of_lt_of_le hlt hx) (lt_irrefl _)

theorem cutRank_insert_of_lt {S : Finset (Fin N)} {c x : Fin N} (hc : c ∉ S) (hx : c < x) :
    cutRank (insert c S) x = cutRank S x + 1 := by
  unfold cutRank
  rw [Finset.filter_insert, if_pos hx,
    Finset.card_insert_of_notMem (fun h => hc (Finset.mem_filter.1 h).1)]

theorem mem_cutU_insert_of_lt {S : Finset (Fin N)} {c x : Fin N} (hc : c ∉ S) (hx : x < c) :
    x ∈ cutU (insert c S) ↔ x ∈ cutU S := by
  have hne : ¬ (x = c) := ne_of_lt hx
  rw [mem_cutU, mem_cutU, cutRank_insert_of_le hc hx.le, Finset.mem_insert]
  simp only [hne, false_or]

theorem mem_cutU_insert_of_gt {S : Finset (Fin N)} {c x : Fin N} (hc : c ∉ S) (hx : c < x) :
    x ∈ cutU (insert c S) ↔ x ∈ cutV S := by
  have hne : ¬ (x = c) := ne_of_gt hx
  rw [mem_cutU, mem_cutV, cutRank_insert_of_lt hc hx, Finset.mem_insert]
  simp only [hne, false_or]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by omega)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by omega)

theorem mem_cutV_insert_of_lt {S : Finset (Fin N)} {c x : Fin N} (hc : c ∉ S) (hx : x < c) :
    x ∈ cutV (insert c S) ↔ x ∈ cutV S := by
  have hne : ¬ (x = c) := ne_of_lt hx
  rw [mem_cutV, mem_cutV, cutRank_insert_of_le hc hx.le, Finset.mem_insert]
  simp only [hne, false_or]

theorem mem_cutV_insert_of_gt {S : Finset (Fin N)} {c x : Fin N} (hc : c ∉ S) (hx : c < x) :
    x ∈ cutV (insert c S) ↔ x ∈ cutU S := by
  have hne : ¬ (x = c) := ne_of_gt hx
  rw [mem_cutV, mem_cutU, cutRank_insert_of_lt hc hx, Finset.mem_insert]
  simp only [hne, false_or]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by omega)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by omega)

theorem mem_cutU_insert_self (S : Finset (Fin N)) (c : Fin N) : c ∈ cutU (insert c S) :=
  subset_cutU _ (Finset.mem_insert_self c S)

theorem mem_cutV_insert_self (S : Finset (Fin N)) (c : Fin N) : c ∈ cutV (insert c S) :=
  subset_cutV _ (Finset.mem_insert_self c S)

/-! ## 2. The threshold pair -/

/-- The left face of the pair that follows the `cutU`-pattern strictly below the
threshold `t` and the `cutV`-pattern from `t` on. -/
def cutLow (S : Finset (Fin N)) (t : ℕ) : Finset (Fin N) :=
  (cutU S).filter (fun x => x.val < t) ∪ (cutV S).filter (fun x => t ≤ x.val)

/-- The right face of the threshold pair: `cutLow` with the two families
exchanged. -/
def cutHigh (S : Finset (Fin N)) (t : ℕ) : Finset (Fin N) :=
  (cutV S).filter (fun x => x.val < t) ∪ (cutU S).filter (fun x => t ≤ x.val)

theorem mem_cutLow {S : Finset (Fin N)} {t : ℕ} {x : Fin N} :
    x ∈ cutLow S t ↔ (x ∈ cutU S ∧ x.val < t) ∨ (x ∈ cutV S ∧ t ≤ x.val) := by
  simp only [cutLow, Finset.mem_union, Finset.mem_filter]

theorem mem_cutHigh {S : Finset (Fin N)} {t : ℕ} {x : Fin N} :
    x ∈ cutHigh S t ↔ (x ∈ cutV S ∧ x.val < t) ∨ (x ∈ cutU S ∧ t ≤ x.val) := by
  simp only [cutHigh, Finset.mem_union, Finset.mem_filter]

theorem mem_cutLow_of_lt {S : Finset (Fin N)} {t : ℕ} {x : Fin N} (h : x.val < t) :
    x ∈ cutLow S t ↔ x ∈ cutU S := by
  rw [mem_cutLow]
  constructor
  · rintro (⟨hx, -⟩ | ⟨-, hx⟩)
    · exact hx
    · omega
  · exact fun hx => Or.inl ⟨hx, h⟩

theorem mem_cutLow_of_ge {S : Finset (Fin N)} {t : ℕ} {x : Fin N} (h : t ≤ x.val) :
    x ∈ cutLow S t ↔ x ∈ cutV S := by
  rw [mem_cutLow]
  constructor
  · rintro (⟨-, hx⟩ | ⟨hx, -⟩)
    · omega
    · exact hx
  · exact fun hx => Or.inr ⟨hx, h⟩

theorem mem_cutHigh_of_lt {S : Finset (Fin N)} {t : ℕ} {x : Fin N} (h : x.val < t) :
    x ∈ cutHigh S t ↔ x ∈ cutV S := by
  rw [mem_cutHigh]
  constructor
  · rintro (⟨hx, -⟩ | ⟨-, hx⟩)
    · exact hx
    · omega
  · exact fun hx => Or.inl ⟨hx, h⟩

theorem mem_cutHigh_of_ge {S : Finset (Fin N)} {t : ℕ} {x : Fin N} (h : t ≤ x.val) :
    x ∈ cutHigh S t ↔ x ∈ cutU S := by
  rw [mem_cutHigh]
  constructor
  · rintro (⟨-, hx⟩ | ⟨hx, -⟩)
    · omega
    · exact hx
  · exact fun hx => Or.inr ⟨hx, h⟩

theorem cutLow_zero (S : Finset (Fin N)) : cutLow S 0 = cutV S := by
  ext x
  exact mem_cutLow_of_ge (Nat.zero_le _)

theorem cutHigh_zero (S : Finset (Fin N)) : cutHigh S 0 = cutU S := by
  ext x
  exact mem_cutHigh_of_ge (Nat.zero_le _)

theorem cutLow_top (S : Finset (Fin N)) : cutLow S N = cutU S := by
  ext x
  exact mem_cutLow_of_lt x.isLt

theorem cutHigh_top (S : Finset (Fin N)) : cutHigh S N = cutV S := by
  ext x
  exact mem_cutHigh_of_lt x.isLt

/-- **Crossing an old cut point changes nothing.**  A cut point lies in both
families, so it is on the correct side of the threshold either way. -/
theorem cutLow_succ_of_mem {S : Finset (Fin N)} {c : Fin N} (hc : c ∈ S) :
    cutLow S (c.val + 1) = cutLow S c.val := by
  ext x
  rcases lt_trichotomy x.val c.val with h | h | h
  · rw [mem_cutLow_of_lt (by omega : x.val < c.val + 1), mem_cutLow_of_lt h]
  · have hx : x = c := Fin.ext h
    subst hx
    rw [mem_cutLow_of_lt (Nat.lt_succ_self x.val), mem_cutLow_of_ge (le_refl x.val)]
    exact ⟨fun _ => subset_cutV _ hc, fun _ => subset_cutU _ hc⟩
  · rw [mem_cutLow_of_ge (by omega : c.val + 1 ≤ x.val), mem_cutLow_of_ge (by omega : c.val ≤ x.val)]

theorem cutHigh_succ_of_mem {S : Finset (Fin N)} {c : Fin N} (hc : c ∈ S) :
    cutHigh S (c.val + 1) = cutHigh S c.val := by
  ext x
  rcases lt_trichotomy x.val c.val with h | h | h
  · rw [mem_cutHigh_of_lt (by omega : x.val < c.val + 1), mem_cutHigh_of_lt h]
  · have hx : x = c := Fin.ext h
    subst hx
    rw [mem_cutHigh_of_lt (Nat.lt_succ_self x.val), mem_cutHigh_of_ge (le_refl x.val)]
    exact ⟨fun _ => subset_cutU _ hc, fun _ => subset_cutV _ hc⟩
  · rw [mem_cutHigh_of_ge (by omega : c.val + 1 ≤ x.val),
      mem_cutHigh_of_ge (by omega : c.val ≤ x.val)]

/-! ## 3. The four descriptions of an inserted cut point -/

section Insert

variable {S : Finset (Fin N)} {c : Fin N}

theorem cutU_insert_erase_eq_cutLow (hc : c ∉ S) (hcU : c ∈ cutU S) :
    (cutU (insert c S)).erase c = cutLow S c.val := by
  ext x
  rcases lt_trichotomy x c with h | rfl | h
  · rw [Finset.mem_erase, mem_cutU_insert_of_lt hc h, mem_cutLow_of_lt (show x.val < c.val from h)]
    exact and_iff_right (ne_of_lt h)
  · rw [mem_cutLow_of_ge (le_refl x.val)]
    constructor
    · intro hx; exact absurd hx (Finset.notMem_erase _ _)
    · intro hx; exact absurd hx (not_mem_cutV_of_mem_cutU hc hcU)
  · rw [Finset.mem_erase, mem_cutU_insert_of_gt hc h,
      mem_cutLow_of_ge (le_of_lt (show c.val < x.val from h))]
    exact and_iff_right (ne_of_gt h)

theorem cutV_insert_eq_cutHigh (hc : c ∉ S) (hcU : c ∈ cutU S) :
    cutV (insert c S) = cutHigh S c.val := by
  ext x
  rcases lt_trichotomy x c with h | rfl | h
  · rw [mem_cutV_insert_of_lt hc h, mem_cutHigh_of_lt (show x.val < c.val from h)]
  · rw [mem_cutHigh_of_ge (le_refl x.val)]
    exact ⟨fun _ => hcU, fun _ => mem_cutV_insert_self S x⟩
  · rw [mem_cutV_insert_of_gt hc h, mem_cutHigh_of_ge (le_of_lt (show c.val < x.val from h))]

theorem cutU_insert_eq_cutLow_succ (hc : c ∉ S) (hcU : c ∈ cutU S) :
    cutU (insert c S) = cutLow S (c.val + 1) := by
  ext x
  rcases lt_trichotomy x c with h | rfl | h
  · rw [mem_cutU_insert_of_lt hc h,
      mem_cutLow_of_lt (by have : x.val < c.val := h; omega : x.val < c.val + 1)]
  · rw [mem_cutLow_of_lt (Nat.lt_succ_self x.val)]
    exact ⟨fun _ => hcU, fun _ => mem_cutU_insert_self S x⟩
  · rw [mem_cutU_insert_of_gt hc h,
      mem_cutLow_of_ge (by have : c.val < x.val := h; omega : c.val + 1 ≤ x.val)]

theorem cutV_insert_erase_eq_cutHigh_succ (hc : c ∉ S) (hcU : c ∈ cutU S) :
    (cutV (insert c S)).erase c = cutHigh S (c.val + 1) := by
  ext x
  rcases lt_trichotomy x c with h | rfl | h
  · rw [Finset.mem_erase, mem_cutV_insert_of_lt hc h,
      mem_cutHigh_of_lt (by have : x.val < c.val := h; omega : x.val < c.val + 1)]
    exact and_iff_right (ne_of_lt h)
  · rw [mem_cutHigh_of_lt (Nat.lt_succ_self x.val)]
    constructor
    · intro hx; exact absurd hx (Finset.notMem_erase _ _)
    · intro hx; exact absurd hx (not_mem_cutV_of_mem_cutU hc hcU)
  · rw [Finset.mem_erase, mem_cutV_insert_of_gt hc h,
      mem_cutHigh_of_ge (by have : c.val < x.val := h; omega : c.val + 1 ≤ x.val)]
    exact and_iff_right (ne_of_gt h)

theorem cutU_insert_eq_cutLow (hc : c ∉ S) (hcU : c ∉ cutU S) :
    cutU (insert c S) = cutLow S c.val := by
  ext x
  rcases lt_trichotomy x c with h | rfl | h
  · rw [mem_cutU_insert_of_lt hc h, mem_cutLow_of_lt (show x.val < c.val from h)]
  · rw [mem_cutLow_of_ge (le_refl x.val)]
    exact ⟨fun _ => mem_cutV_of_not_mem_cutU hcU, fun _ => mem_cutU_insert_self S x⟩
  · rw [mem_cutU_insert_of_gt hc h, mem_cutLow_of_ge (le_of_lt (show c.val < x.val from h))]

theorem cutV_insert_erase_eq_cutHigh (hc : c ∉ S) (hcU : c ∉ cutU S) :
    (cutV (insert c S)).erase c = cutHigh S c.val := by
  ext x
  rcases lt_trichotomy x c with h | rfl | h
  · rw [Finset.mem_erase, mem_cutV_insert_of_lt hc h, mem_cutHigh_of_lt (show x.val < c.val from h)]
    exact and_iff_right (ne_of_lt h)
  · rw [mem_cutHigh_of_ge (le_refl x.val)]
    constructor
    · intro hx; exact absurd hx (Finset.notMem_erase _ _)
    · intro hx; exact absurd hx hcU
  · rw [Finset.mem_erase, mem_cutV_insert_of_gt hc h,
      mem_cutHigh_of_ge (le_of_lt (show c.val < x.val from h))]
    exact and_iff_right (ne_of_gt h)

theorem cutU_insert_erase_eq_cutLow_succ (hc : c ∉ S) (hcU : c ∉ cutU S) :
    (cutU (insert c S)).erase c = cutLow S (c.val + 1) := by
  ext x
  rcases lt_trichotomy x c with h | rfl | h
  · rw [Finset.mem_erase, mem_cutU_insert_of_lt hc h,
      mem_cutLow_of_lt (by have : x.val < c.val := h; omega : x.val < c.val + 1)]
    exact and_iff_right (ne_of_lt h)
  · rw [mem_cutLow_of_lt (Nat.lt_succ_self x.val)]
    constructor
    · intro hx; exact absurd hx (Finset.notMem_erase _ _)
    · intro hx; exact absurd hx hcU
  · rw [Finset.mem_erase, mem_cutU_insert_of_gt hc h,
      mem_cutLow_of_ge (by have : c.val < x.val := h; omega : c.val + 1 ≤ x.val)]
    exact and_iff_right (ne_of_gt h)

theorem cutV_insert_eq_cutHigh_succ (hc : c ∉ S) (hcU : c ∉ cutU S) :
    cutV (insert c S) = cutHigh S (c.val + 1) := by
  ext x
  rcases lt_trichotomy x c with h | rfl | h
  · rw [mem_cutV_insert_of_lt hc h,
      mem_cutHigh_of_lt (by have : x.val < c.val := h; omega : x.val < c.val + 1)]
  · rw [mem_cutHigh_of_lt (Nat.lt_succ_self x.val)]
    exact ⟨fun _ => mem_cutV_of_not_mem_cutU hcU, fun _ => mem_cutV_insert_self S x⟩
  · rw [mem_cutV_insert_of_gt hc h,
      mem_cutHigh_of_ge (by have : c.val < x.val := h; omega : c.val + 1 ≤ x.val)]

end Insert

/-! ## 4. Telescoping in characteristic two -/

theorem telescope_char2 {M : Type*} [AddCommGroup M] (h2 : ∀ x : M, x + x = 0)
    (Ξ : ℕ → M) (n : ℕ) :
    ∑ j ∈ Finset.range n, (Ξ j + Ξ (j + 1)) = Ξ 0 + Ξ n := by
  induction n with
  | zero => rw [Finset.sum_range_zero, h2]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hrw : (Ξ 0 + Ξ n) + (Ξ n + Ξ (n + 1)) = (Ξ n + Ξ n) + (Ξ 0 + Ξ (n + 1)) := by abel
      rw [hrw, h2, zero_add]

/-- **The cancellation.**  Summing, over all vertices `c` that are not yet cut
points, the two ways of turning `c` into a cut point and deleting it again from
one of the two faces, leaves exactly the two orders of the original cut. -/
theorem cut_insert_cancel {M : Type*} [AddCommGroup M] (h2 : ∀ x : M, x + x = 0)
    (Θ : Finset (Fin N) → Finset (Fin N) → M) (S : Finset (Fin N)) :
    ∑ c ∈ Sᶜ, (Θ ((cutU (insert c S)).erase c) (cutV (insert c S))
             + Θ (cutU (insert c S)) ((cutV (insert c S)).erase c))
      = Θ (cutU S) (cutV S) + Θ (cutV S) (cutU S) := by
  classical
  have key : ∀ c ∈ (Sᶜ : Finset (Fin N)),
      Θ ((cutU (insert c S)).erase c) (cutV (insert c S))
        + Θ (cutU (insert c S)) ((cutV (insert c S)).erase c)
      = Θ (cutLow S c.val) (cutHigh S c.val)
        + Θ (cutLow S (c.val + 1)) (cutHigh S (c.val + 1)) := by
    intro c hc'
    have hc : c ∉ S := Finset.mem_compl.1 hc'
    by_cases hcU : c ∈ cutU S
    · rw [cutU_insert_erase_eq_cutLow hc hcU, cutV_insert_erase_eq_cutHigh_succ hc hcU,
        cutV_insert_eq_cutHigh hc hcU, cutU_insert_eq_cutLow_succ hc hcU]
    · rw [cutU_insert_erase_eq_cutLow_succ hc hcU, cutV_insert_erase_eq_cutHigh hc hcU,
        cutV_insert_eq_cutHigh_succ hc hcU, cutU_insert_eq_cutLow hc hcU]
      exact add_comm _ _
  have hzero : ∀ c ∈ S,
      Θ (cutLow S c.val) (cutHigh S c.val)
        + Θ (cutLow S (c.val + 1)) (cutHigh S (c.val + 1)) = 0 := by
    intro c hc
    rw [cutLow_succ_of_mem hc, cutHigh_succ_of_mem hc]
    exact h2 _
  calc
    ∑ c ∈ Sᶜ, (Θ ((cutU (insert c S)).erase c) (cutV (insert c S))
             + Θ (cutU (insert c S)) ((cutV (insert c S)).erase c))
        = ∑ c ∈ Sᶜ, (Θ (cutLow S c.val) (cutHigh S c.val)
             + Θ (cutLow S (c.val + 1)) (cutHigh S (c.val + 1))) := Finset.sum_congr rfl key
    _ = ∑ c : Fin N, (Θ (cutLow S c.val) (cutHigh S c.val)
             + Θ (cutLow S (c.val + 1)) (cutHigh S (c.val + 1))) := by
          rw [← Finset.sum_add_sum_compl S
            (fun c : Fin N => Θ (cutLow S c.val) (cutHigh S c.val)
               + Θ (cutLow S (c.val + 1)) (cutHigh S (c.val + 1))),
            Finset.sum_eq_zero hzero, zero_add]
    _ = ∑ j ∈ Finset.range N, (Θ (cutLow S j) (cutHigh S j)
             + Θ (cutLow S (j + 1)) (cutHigh S (j + 1))) :=
          Fin.sum_univ_eq_sum_range
            (fun j => Θ (cutLow S j) (cutHigh S j)
               + Θ (cutLow S (j + 1)) (cutHigh S (j + 1))) N
    _ = Θ (cutLow S 0) (cutHigh S 0) + Θ (cutLow S N) (cutHigh S N) :=
          telescope_char2 h2 (fun j => Θ (cutLow S j) (cutHigh S j)) N
    _ = Θ (cutV S) (cutU S) + Θ (cutU S) (cutV S) := by
          rw [cutLow_zero, cutHigh_zero, cutLow_top, cutHigh_top]
    _ = Θ (cutU S) (cutV S) + Θ (cutV S) (cutU S) := add_comm _ _

/-! ## 5. Reindexing the two sums that meet the cancellation -/

/-- Summing over cut sets of size `i+2` together with a chosen cut point is the
same as summing over cut sets of size `i+1` together with a non-cut point. -/
theorem sum_cutIndex_succ_erase {M : Type*} [AddCommMonoid M] (i n : ℕ)
    (G : Finset (Fin (n + 1)) → Fin (n + 1) → M) :
    ∑ T ∈ cutIndex (i + 1) n, ∑ c ∈ T, G (T.erase c) c
      = ∑ T ∈ cutIndex i n, ∑ c ∈ Tᶜ, G T c := by
  classical
  have step : ∀ c : Fin (n + 1),
      ∑ T ∈ (cutIndex (i + 1) n).filter (fun T => c ∈ T), G (T.erase c) c
        = ∑ T ∈ (cutIndex i n).filter (fun T => c ∉ T), G T c := by
    intro c
    refine Finset.sum_nbij' (fun T => T.erase c) (fun T => insert c T) ?_ ?_ ?_ ?_ ?_
    · intro T hT
      obtain ⟨hT1, hT2⟩ := Finset.mem_filter.1 hT
      have hcard : (T.erase c).card = T.card - 1 := Finset.card_erase_of_mem hT2
      have hT1' : T.card = i + 1 + 1 := mem_cutIndex.1 hT1
      refine Finset.mem_filter.2 ⟨mem_cutIndex.2 (by omega), Finset.notMem_erase _ _⟩
    · intro T hT
      obtain ⟨hT1, hT2⟩ := Finset.mem_filter.1 hT
      have hcard : (insert c T).card = T.card + 1 := Finset.card_insert_of_notMem hT2
      have hT1' : T.card = i + 1 := mem_cutIndex.1 hT1
      exact Finset.mem_filter.2 ⟨mem_cutIndex.2 (by omega), Finset.mem_insert_self c T⟩
    · intro T hT
      exact Finset.insert_erase (Finset.mem_filter.1 hT).2
    · intro T hT
      exact Finset.erase_insert (Finset.mem_filter.1 hT).2
    · intro _ _
      rfl
  calc
    ∑ T ∈ cutIndex (i + 1) n, ∑ c ∈ T, G (T.erase c) c
        = ∑ T ∈ cutIndex (i + 1) n, ∑ c : Fin (n + 1),
            if c ∈ T then G (T.erase c) c else 0 := by
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [← Finset.sum_filter, Finset.filter_univ_mem]
    _ = ∑ c : Fin (n + 1), ∑ T ∈ cutIndex (i + 1) n,
            if c ∈ T then G (T.erase c) c else 0 := Finset.sum_comm
    _ = ∑ c : Fin (n + 1), ∑ T ∈ (cutIndex (i + 1) n).filter (fun T => c ∈ T),
            G (T.erase c) c := by
          refine Finset.sum_congr rfl fun c _ => (Finset.sum_filter _ _).symm
    _ = ∑ c : Fin (n + 1), ∑ T ∈ (cutIndex i n).filter (fun T => c ∉ T), G T c :=
          Finset.sum_congr rfl fun c _ => step c
    _ = ∑ c : Fin (n + 1), ∑ T ∈ cutIndex i n, if c ∉ T then G T c else 0 :=
          Finset.sum_congr rfl fun c _ => Finset.sum_filter _ _
    _ = ∑ T ∈ cutIndex i n, ∑ c : Fin (n + 1), if c ∉ T then G T c else 0 := Finset.sum_comm
    _ = ∑ T ∈ cutIndex i n, ∑ c ∈ Tᶜ, G T c := by
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]

/-! ## 6. Deleting a vertex of the ambient simplex -/

@[simp]
theorem succAboveEmb_apply {n : ℕ} (k : Fin (n + 1)) (x : Fin n) :
    (Fin.succAboveOrderEmb k).toEmbedding x = k.succAbove x := rfl

theorem cutRank_map_succAbove {n : ℕ} (k : Fin (n + 2)) (S : Finset (Fin (n + 1)))
    (y : Fin (n + 1)) :
    cutRank (S.map (Fin.succAboveOrderEmb k).toEmbedding) (k.succAbove y) = cutRank S y := by
  unfold cutRank
  have hset : (S.map (Fin.succAboveOrderEmb k).toEmbedding).filter
        (fun c => c < k.succAbove y)
      = (S.filter (fun c => c < y)).map (Fin.succAboveOrderEmb k).toEmbedding := by
    ext z
    constructor
    · intro hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
      obtain ⟨w, hwS, rfl⟩ := Finset.mem_map.1 hz1
      refine Finset.mem_map.2 ⟨w, Finset.mem_filter.2 ⟨hwS, ?_⟩, rfl⟩
      exact (Fin.strictMono_succAbove k).lt_iff_lt.1 hz2
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hz
      obtain ⟨hw1, hw2⟩ := Finset.mem_filter.1 hw
      exact Finset.mem_filter.2 ⟨Finset.mem_map.2 ⟨w, hw1, rfl⟩,
        (Fin.strictMono_succAbove k).lt_iff_lt.2 hw2⟩
  rw [hset, Finset.card_map]

theorem cutU_map_succAbove {n : ℕ} (k : Fin (n + 2)) (S : Finset (Fin (n + 1))) :
    (cutU S).map (Fin.succAboveOrderEmb k).toEmbedding
      = (cutU (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hz
    refine Finset.mem_erase.2 ⟨Fin.succAbove_ne k y, ?_⟩
    rw [mem_cutU, cutRank_map_succAbove]
    rcases mem_cutU.1 hy with h | h
    · exact Or.inl (Finset.mem_map_of_mem _ h)
    · exact Or.inr h
  · intro hz
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hz
    obtain ⟨y, rfl⟩ := Fin.exists_succAbove_eq hne
    rw [mem_cutU, cutRank_map_succAbove] at hmem
    refine Finset.mem_map.2 ⟨y, ?_, rfl⟩
    rw [mem_cutU]
    rcases hmem with h | h
    · obtain ⟨w, hw, hwe⟩ := Finset.mem_map.1 h
      have hwy : w = y := (Fin.strictMono_succAbove k).injective hwe
      exact Or.inl (hwy ▸ hw)
    · exact Or.inr h

theorem cutV_map_succAbove {n : ℕ} (k : Fin (n + 2)) (S : Finset (Fin (n + 1))) :
    (cutV S).map (Fin.succAboveOrderEmb k).toEmbedding
      = (cutV (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hz
    refine Finset.mem_erase.2 ⟨Fin.succAbove_ne k y, ?_⟩
    rw [mem_cutV, cutRank_map_succAbove]
    rcases mem_cutV.1 hy with h | h
    · exact Or.inl (Finset.mem_map_of_mem _ h)
    · exact Or.inr h
  · intro hz
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hz
    obtain ⟨y, rfl⟩ := Fin.exists_succAbove_eq hne
    rw [mem_cutV, cutRank_map_succAbove] at hmem
    refine Finset.mem_map.2 ⟨y, ?_, rfl⟩
    rw [mem_cutV]
    rcases hmem with h | h
    · obtain ⟨w, hw, hwe⟩ := Finset.mem_map.1 h
      have hwy : w = y := (Fin.strictMono_succAbove k).injective hwe
      exact Or.inl (hwy ▸ hw)
    · exact Or.inr h

/-- Reindexing the cut sets of a boundary face as the cut sets of the simplex
that avoid the deleted vertex. -/
theorem sum_cutIndex_map {M : Type*} [AddCommMonoid M] (i n : ℕ) (k : Fin (n + 2))
    (F : Finset (Fin (n + 2)) → M) :
    ∑ S ∈ cutIndex i n, F (S.map (Fin.succAboveOrderEmb k).toEmbedding)
      = ∑ T ∈ (cutIndex i (n + 1)).filter (fun T => k ∉ T), F T := by
  classical
  refine Finset.sum_bij (fun S _ => S.map (Fin.succAboveOrderEmb k).toEmbedding) ?_ ?_ ?_ ?_
  · intro S hS
    refine Finset.mem_filter.2 ⟨mem_cutIndex.2 ?_, ?_⟩
    · rw [Finset.card_map]; exact mem_cutIndex.1 hS
    · intro hk
      obtain ⟨y, -, hy⟩ := Finset.mem_map.1 hk
      exact Fin.succAbove_ne k y hy
  · intro S1 _ S2 _ heq
    exact Finset.map_injective _ heq
  · intro T hT
    obtain ⟨hT1, hT2⟩ := Finset.mem_filter.1 hT
    refine ⟨Finset.univ.filter (fun y => k.succAbove y ∈ T), ?_, ?_⟩
    · rw [mem_cutIndex]
      have hmap : (Finset.univ.filter (fun y => k.succAbove y ∈ T)).map
          (Fin.succAboveOrderEmb k).toEmbedding = T := by
        ext z
        constructor
        · intro hz
          obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hz
          exact (Finset.mem_filter.1 hy).2
        · intro hz
          have hzk : z ≠ k := fun hh => hT2 (hh ▸ hz)
          obtain ⟨y, rfl⟩ := Fin.exists_succAbove_eq hzk
          exact Finset.mem_map.2 ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ y, hz⟩, rfl⟩
      have := congrArg Finset.card hmap
      rw [Finset.card_map] at this
      rw [this]
      exact mem_cutIndex.1 hT1
    · ext z
      constructor
      · intro hz
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hz
        exact (Finset.mem_filter.1 hy).2
      · intro hz
        have hzk : z ≠ k := fun hh => hT2 (hh ▸ hz)
        obtain ⟨y, rfl⟩ := Fin.exists_succAbove_eq hzk
        exact Finset.mem_map.2 ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ y, hz⟩, rfl⟩
  · intro _ _
    rfl

end CharClass
end GroupApproximation
