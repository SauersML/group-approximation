import GroupApproximation.CharClass.SteenrodCutCancel
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Ring.Commute

/-!
# The sign of Steenrod's cup-1 product

Over `ZMod 2` the cup-`i` products carry no signs (`SteenrodCochain.cochainCupI`),
and the coboundary formula of `SteenrodCoboundary.lean` is proved with `x + x = 0`
doing the cancelling.  Over an arbitrary commutative ring each cut carries a sign,
and this file is the arithmetic of that sign.  No cochain and no simplex appears
here: everything is `Finset (Fin N)` combinatorics, exactly as in `SteenrodCut.lean`.

## The sign

For a cut `S` of an `n`-simplex,

```text
cutExp S = ((cutU S).card + 1) * (cutV S).card + ∏ c ∈ S, (c : ℕ)
cupOneSign K S = (-1 : K) ^ cutExp S.
```

On the cuts that survive the bidegree test (`|cutU S| = a+1`, `|cutV S| = b+1`,
`S = {c₀ < c₁}`) this is `(-1)^(a + a*b + c₀*c₁)`, which is the closed form an exact
linear solve produced (`scratch/sp-cupone/cupone_signs.py`: the coboundary formula
with an unknown sign on each cut and the two Leibniz coefficients pinned at `1` and
`(-1)^a is a linear system; over all bidegrees `0 ≤ a, b ≤ 5` it is consistent, has
no free parameter, and every solved value is `±1`).

**Why it is written through the face cardinalities and not through the bidegree.**
The `ZMod 2` proof never case-splits on degree — off the bidegree every term is `0`
because `faceVal` is, and the identity is proved termwise.  A sign spelled
`(-1)^(a + a*b + c₀*c₁)` makes the termwise sign identity *false* off the bidegree,
which would force a degree case split through the whole development.  Spelled
`cutExp`, the two identities the coboundary formula needs
(`cutExp_succAbove_cutU`, `cutExp_succAbove_cutV`) hold for **every** two-point cut
and **every** vertex outside it, with no hypothesis on degrees.

## The two identities

Deleting the vertex `k` of an `(n+1)`-simplex sends a two-point cut `S` of the face
to the cut `T = S.map (succAbove k)` of the simplex, and `k` lands in exactly one of
the two families of `T`.  Then

```text
k ∈ cutU T :  k + cutExp S ≡ cutExp T + cutRank (cutU T) k                        (mod 2)
k ∈ cutV T :  k + cutExp S ≡ ((cutU T).card - 1) + cutExp T + cutRank (cutV T) k  (mod 2)
```

Three positions of `k` relative to `c₀ < c₁` separate the cases, and in each the two
`(card + 1) * card` terms differ by a single factor while the two products `∏` differ
by a linear amount, so each case is linear arithmetic once that one multiplication is
abstracted (`sign_arith_left`, `sign_arith_right`).
-/

namespace GroupApproximation
namespace CharClass

/-! ## 0. Signs from parities

The file computes exponents in `ℕ` and compares them modulo two; this is the only
bridge to the coefficient ring. -/

/-- Two exponents of the same parity give the same sign. -/
theorem neg_one_pow_congr_mod_two {K : Type} [CommRing K] {m m' : ℕ} (h : m % 2 = m' % 2) :
    (-1 : K) ^ m = (-1 : K) ^ m' := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

/-! ## 1. Two-point cuts -/

variable {N : ℕ}

/-- A two-element set of `Fin N`, listed in order. -/
theorem exists_pair_of_card_two {S : Finset (Fin N)} (hS : S.card = 2) :
    ∃ c₀ c₁ : Fin N, c₀ < c₁ ∧ S = {c₀, c₁} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hS
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨a, b, h, rfl⟩
  · exact ⟨b, a, h, Finset.pair_comm a b⟩

theorem card_pair {t₀ t₁ : Fin N} (hne : t₀ ≠ t₁) :
    ({t₀, t₁} : Finset (Fin N)).card = 2 := by
  rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hne),
    Finset.card_singleton]

/-- The cut-rank of a vertex in a two-point cut counts the two cut points below it. -/
theorem cutRank_pair {t₀ t₁ : Fin N} (hne : t₀ ≠ t₁) (x : Fin N) :
    cutRank ({t₀, t₁} : Finset (Fin N)) x
      = (if t₀ < x then 1 else 0) + (if t₁ < x then 1 else 0) := by
  classical
  unfold cutRank
  rw [Finset.filter_insert, Finset.filter_singleton]
  have hmem : t₀ ∉ ({t₁} : Finset (Fin N)) := by
    rw [Finset.mem_singleton]
    exact hne
  by_cases h0 : t₀ < x
  · by_cases h1 : t₁ < x
    · rw [if_pos h1, if_pos h0, if_pos h0, if_pos h1,
        Finset.card_insert_of_notMem hmem, Finset.card_singleton]
    · rw [if_neg h1, if_pos h0, if_pos h0, if_neg h1,
        Finset.card_insert_of_notMem (Finset.notMem_empty t₀), Finset.card_empty]
  · by_cases h1 : t₁ < x
    · rw [if_pos h1, if_neg h0, if_neg h0, if_pos h1, Finset.card_singleton]
    · rw [if_neg h1, if_neg h0, if_neg h0, if_neg h1, Finset.card_empty]

/-- Membership in a two-element set, read on the underlying naturals.  `omega` cannot
see an equality of `Fin`s, so the conversion is done here rather than by `simp`. -/
theorem mem_pair_val {t₀ t₁ : Fin N} (x : Fin N) :
    x ∈ ({t₀, t₁} : Finset (Fin N)) ↔ (x.val = t₀.val ∨ x.val = t₁.val) := by
  rw [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (hx | hx)
    · exact Or.inl (Fin.ext hx)
    · exact Or.inr (Fin.ext hx)

/-- **The left family of a two-point cut**: the initial segment up to the first cut
point together with the final segment from the second on. -/
theorem mem_cutU_pair {t₀ t₁ : Fin N} (h : t₀ < t₁) (x : Fin N) :
    x ∈ cutU ({t₀, t₁} : Finset (Fin N)) ↔ (x.val ≤ t₀.val ∨ t₁.val ≤ x.val) := by
  have hlt : t₀.val < t₁.val := h
  rw [mem_cutU, cutRank_pair (ne_of_lt h) x, mem_pair_val x]
  by_cases h0 : t₀ < x
  · have h0' : t₀.val < x.val := h0
    by_cases h1 : t₁ < x
    · have h1' : t₁.val < x.val := h1
      rw [if_pos h0, if_pos h1]
      omega
    · have h1' : ¬ t₁.val < x.val := h1
      rw [if_pos h0, if_neg h1]
      omega
  · have h0' : ¬ t₀.val < x.val := h0
    by_cases h1 : t₁ < x
    · have h1' : t₁.val < x.val := h1
      rw [if_neg h0, if_pos h1]
      omega
    · have h1' : ¬ t₁.val < x.val := h1
      rw [if_neg h0, if_neg h1]
      omega

/-- **The right family of a two-point cut**: the closed interval between the two cut
points. -/
theorem mem_cutV_pair {t₀ t₁ : Fin N} (h : t₀ < t₁) (x : Fin N) :
    x ∈ cutV ({t₀, t₁} : Finset (Fin N)) ↔ (t₀.val ≤ x.val ∧ x.val ≤ t₁.val) := by
  have hlt : t₀.val < t₁.val := h
  rw [mem_cutV, cutRank_pair (ne_of_lt h) x, mem_pair_val x]
  by_cases h0 : t₀ < x
  · have h0' : t₀.val < x.val := h0
    by_cases h1 : t₁ < x
    · have h1' : t₁.val < x.val := h1
      rw [if_pos h0, if_pos h1]
      omega
    · have h1' : ¬ t₁.val < x.val := h1
      rw [if_pos h0, if_neg h1]
      omega
  · have h0' : ¬ t₀.val < x.val := h0
    by_cases h1 : t₁ < x
    · have h1' : t₁.val < x.val := h1
      rw [if_neg h0, if_pos h1]
      omega
    · have h1' : ¬ t₁.val < x.val := h1
      rw [if_neg h0, if_neg h1]
      omega

theorem cutU_pair_eq {t₀ t₁ : Fin N} (h : t₀ < t₁) :
    cutU ({t₀, t₁} : Finset (Fin N)) = Finset.Iic t₀ ∪ Finset.Ici t₁ := by
  ext x
  rw [mem_cutU_pair h, Finset.mem_union, Finset.mem_Iic, Finset.mem_Ici, Fin.le_def, Fin.le_def]

theorem cutV_pair_eq {t₀ t₁ : Fin N} (h : t₀ < t₁) :
    cutV ({t₀, t₁} : Finset (Fin N)) = Finset.Icc t₀ t₁ := by
  ext x
  rw [mem_cutV_pair h, Finset.mem_Icc, Fin.le_def, Fin.le_def]

theorem card_cutU_pair {t₀ t₁ : Fin N} (h : t₀ < t₁) :
    (cutU ({t₀, t₁} : Finset (Fin N))).card = t₀.val + 1 + (N - t₁.val) := by
  have hlt : t₀.val < t₁.val := h
  have hd : Finset.Iic t₀ ∩ Finset.Ici t₁ = (∅ : Finset (Fin N)) := by
    ext x
    rw [Finset.mem_inter, Finset.mem_Iic, Finset.mem_Ici, Fin.le_def, Fin.le_def]
    constructor
    · rintro ⟨h1, h2⟩
      omega
    · intro hx
      exact absurd hx (Finset.notMem_empty x)
  have hcard := Finset.card_union_add_card_inter (Finset.Iic t₀) (Finset.Ici t₁)
  rw [hd, Finset.card_empty, Fin.card_Iic, Fin.card_Ici] at hcard
  rw [cutU_pair_eq h]
  omega

theorem card_cutV_pair {t₀ t₁ : Fin N} (h : t₀ < t₁) :
    (cutV ({t₀, t₁} : Finset (Fin N))).card = t₁.val + 1 - t₀.val := by
  rw [cutV_pair_eq h, Fin.card_Icc]

theorem prod_pair {t₀ t₁ : Fin N} (hne : t₀ ≠ t₁) :
    ∏ c ∈ ({t₀, t₁} : Finset (Fin N)), (c : ℕ) = t₀.val * t₁.val := by
  have hmem : t₀ ∉ ({t₁} : Finset (Fin N)) := by
    rw [Finset.mem_singleton]
    exact hne
  rw [Finset.prod_insert hmem, Finset.prod_singleton]

/-! ## 2. The rank of a vertex in the two families -/

/-- **The two ranks add up.**  Intersecting `cutU_union_cutV` and `cutU_inter_cutV`
with the vertices below `x` gives the same inclusion–exclusion. -/
theorem cutRank_cutU_add_cutRank_cutV (S : Finset (Fin N)) (x : Fin N) :
    cutRank (cutU S) x + cutRank (cutV S) x = x.val + cutRank S x := by
  classical
  unfold cutRank
  have hu : (cutU S).filter (fun c => c < x) ∪ (cutV S).filter (fun c => c < x)
      = Finset.univ.filter (fun c : Fin N => c < x) := by
    ext c
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨-, hc⟩ | ⟨-, hc⟩) <;> exact hc
    · intro hc
      have hmem : c ∈ cutU S ∪ cutV S := by
        rw [cutU_union_cutV]
        exact Finset.mem_univ c
      rcases Finset.mem_union.1 hmem with h | h
      · exact Or.inl ⟨h, hc⟩
      · exact Or.inr ⟨h, hc⟩
  have hi : (cutU S).filter (fun c => c < x) ∩ (cutV S).filter (fun c => c < x)
      = S.filter (fun c => c < x) := by
    ext c
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hU, hc⟩, ⟨hV, -⟩⟩
      refine ⟨?_, hc⟩
      rw [← cutU_inter_cutV S]
      exact Finset.mem_inter.2 ⟨hU, hV⟩
    · rintro ⟨hS, hc⟩
      exact ⟨⟨subset_cutU S hS, hc⟩, ⟨subset_cutV S hS, hc⟩⟩
  have hseg : (Finset.univ.filter (fun c : Fin N => c < x)).card = x.val := by
    have he : (Finset.univ.filter (fun c : Fin N => c < x)) = Finset.Iio x := by
      ext c
      rw [Finset.mem_filter, Finset.mem_Iio]
      exact ⟨fun hc => hc.2, fun hc => ⟨Finset.mem_univ c, hc⟩⟩
    rw [he, Fin.card_Iio]
  have hcard := Finset.card_union_add_card_inter ((cutU S).filter (fun c => c < x))
    ((cutV S).filter (fun c => c < x))
  rw [hu, hi, hseg] at hcard
  omega

/-- The rank of a vertex in the right family of a two-point cut. -/
theorem cutRank_cutV_pair {t₀ t₁ : Fin N} (h : t₀ < t₁) (k : Fin N) :
    cutRank (cutV ({t₀, t₁} : Finset (Fin N))) k
      = if k.val ≤ t₁.val then k.val - t₀.val else t₁.val + 1 - t₀.val := by
  classical
  have hlt : t₀.val < t₁.val := h
  unfold cutRank
  rw [cutV_pair_eq h]
  by_cases hk : k.val ≤ t₁.val
  · rw [if_pos hk]
    have he : (Finset.Icc t₀ t₁).filter (fun c => c < k) = Finset.Ico t₀ k := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, Fin.le_def, Fin.lt_def]
      omega
    rw [he, Fin.card_Ico]
  · rw [if_neg hk]
    have he : (Finset.Icc t₀ t₁).filter (fun c => c < k) = Finset.Icc t₀ t₁ := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_Icc, Fin.le_def, Fin.lt_def]
      omega
    rw [he, Fin.card_Icc]

/-! ## 3. The exponent of a cut, and the sign -/

/-- **The exponent of a cut**, written through the cardinalities of the two families
rather than through the bidegree, so that the termwise identities of §5 hold with no
degree hypothesis. -/
def cutExp (S : Finset (Fin N)) : ℕ :=
  ((cutU S).card + 1) * (cutV S).card + ∏ c ∈ S, (c : ℕ)

/-- **The sign of a cut**, in the coefficient ring. -/
def cupOneSign (K : Type) [CommRing K] (S : Finset (Fin N)) : K :=
  (-1 : K) ^ cutExp S

theorem cupOneSign_def {K : Type} [CommRing K] (S : Finset (Fin N)) :
    cupOneSign K S = (-1 : K) ^ cutExp S := rfl

/-- The exponent of a two-point cut, in closed form. -/
theorem cutExp_pair {t₀ t₁ : Fin N} (h : t₀ < t₁) :
    cutExp ({t₀, t₁} : Finset (Fin N))
      = (t₀.val + 1 + (N - t₁.val) + 1) * (t₁.val + 1 - t₀.val) + t₀.val * t₁.val := by
  unfold cutExp
  rw [card_cutU_pair h, card_cutV_pair h, prod_pair (ne_of_lt h)]

/-! ## 4. Deleting a vertex of the ambient simplex

The only multiplication in the sign is `(card + 1) * card`.  In each of the three
positions of the deleted vertex the two cuts' factors differ by a single `+ 1`, so
one `ring` step relates the two products and everything else is linear: `omega`
finishes with the products left as atoms. -/

theorem val_succAbove_of_lt {n : ℕ} (k : Fin (n + 2)) (c : Fin (n + 1)) (h : c.val < k.val) :
    (k.succAbove c).val = c.val := by
  rw [Fin.succAbove_of_castSucc_lt k c (by rw [Fin.lt_def]; exact h)]
  rfl

theorem val_succAbove_of_ge {n : ℕ} (k : Fin (n + 2)) (c : Fin (n + 1)) (h : k.val ≤ c.val) :
    (k.succAbove c).val = c.val + 1 := by
  rw [Fin.succAbove_of_le_castSucc k c (by rw [Fin.le_def]; exact h)]
  rfl

theorem succAbove_lt_succAbove {n : ℕ} (k : Fin (n + 2)) {c₀ c₁ : Fin (n + 1)} (h : c₀ < c₁) :
    k.succAbove c₀ < k.succAbove c₁ :=
  Fin.strictMono_succAbove k h

theorem map_pair {n : ℕ} (k : Fin (n + 2)) (c₀ c₁ : Fin (n + 1)) :
    ({c₀, c₁} : Finset (Fin (n + 1))).map (Fin.succAboveOrderEmb k).toEmbedding
      = {k.succAbove c₀, k.succAbove c₁} := by
  rw [Finset.map_insert, Finset.map_singleton]
  rfl

/-- Which family the deleted vertex lands in: the left one exactly when it is outside
the interval spanned by the cut. -/
theorem mem_cutU_map_pair {n : ℕ} (k : Fin (n + 2)) {c₀ c₁ : Fin (n + 1)} (h : c₀ < c₁) :
    k ∈ cutU ({k.succAbove c₀, k.succAbove c₁} : Finset (Fin (n + 2)))
      ↔ (k.val ≤ c₀.val ∨ c₁.val < k.val) := by
  have hlt : c₀.val < c₁.val := h
  rw [mem_cutU_pair (succAbove_lt_succAbove k h) k]
  by_cases h0 : k.val ≤ c₀.val
  · rw [val_succAbove_of_ge k c₀ h0, val_succAbove_of_ge k c₁ (by omega)]
    omega
  · by_cases h1 : k.val ≤ c₁.val
    · rw [val_succAbove_of_lt k c₀ (by omega), val_succAbove_of_ge k c₁ h1]
      omega
    · rw [val_succAbove_of_lt k c₀ (by omega), val_succAbove_of_lt k c₁ (by omega)]
      omega

/-- **Termwise sign identity, left family.**  When the deleted vertex lands in the
left family, the sign of the small cut times `(-1)^k` is the sign of the big cut
times the position sign of `k` in that family. -/
theorem cutExp_succAbove_cutU {n : ℕ} (k : Fin (n + 2)) {c₀ c₁ : Fin (n + 1)} (h : c₀ < c₁)
    (hk : k.val ≤ c₀.val ∨ c₁.val < k.val) :
    (k.val + cutExp ({c₀, c₁} : Finset (Fin (n + 1)))) % 2
      = (cutExp ({k.succAbove c₀, k.succAbove c₁} : Finset (Fin (n + 2)))
          + cutRank (cutU ({k.succAbove c₀, k.succAbove c₁} : Finset (Fin (n + 2)))) k) % 2 := by
  have hlt : c₀.val < c₁.val := h
  have hc₁ : c₁.val < n + 1 := c₁.isLt
  have hT : k.succAbove c₀ < k.succAbove c₁ := succAbove_lt_succAbove k h
  have hne : k.succAbove c₀ ≠ k.succAbove c₁ := ne_of_lt hT
  have hrankSum := cutRank_cutU_add_cutRank_cutV
    ({k.succAbove c₀, k.succAbove c₁} : Finset (Fin (n + 2))) k
  rw [cutRank_pair hne k, cutRank_cutV_pair hT k] at hrankSum
  rw [cutExp_pair h, cutExp_pair hT]
  rcases hk with hk | hk
  · -- the deleted vertex is below both cut points
    have e0 : (k.succAbove c₀).val = c₀.val + 1 := val_succAbove_of_ge k c₀ hk
    have e1 : (k.succAbove c₁).val = c₁.val + 1 := val_succAbove_of_ge k c₁ (by omega)
    have hlt0 : ¬ (k.succAbove c₀ < k) := by
      rw [Fin.lt_def, e0]
      omega
    have hlt1 : ¬ (k.succAbove c₁ < k) := by
      rw [Fin.lt_def, e1]
      omega
    rw [e0, e1, if_neg hlt0, if_neg hlt1,
      if_pos (show k.val ≤ c₁.val + 1 by omega)] at hrankSum
    rw [e0, e1]
    have hf1 : c₀.val + 1 + 1 + (n + 2 - (c₁.val + 1)) + 1
        = c₀.val + 1 + (n + 1 - c₁.val) + 1 + 1 := by omega
    have hf2 : c₁.val + 1 + 1 - (c₀.val + 1) = c₁.val + 1 - c₀.val := by omega
    rw [hf1, hf2]
    have hmul : (c₀.val + 1 + (n + 1 - c₁.val) + 1 + 1) * (c₁.val + 1 - c₀.val)
        = (c₀.val + 1 + (n + 1 - c₁.val) + 1) * (c₁.val + 1 - c₀.val)
          + (c₁.val + 1 - c₀.val) := by ring
    have hp : (c₀.val + 1) * (c₁.val + 1)
        = c₀.val * c₁.val + (c₀.val + c₁.val + 1) := by ring
    rw [hmul, hp]
    omega
  · -- the deleted vertex is above both cut points
    have e0 : (k.succAbove c₀).val = c₀.val := val_succAbove_of_lt k c₀ (by omega)
    have e1 : (k.succAbove c₁).val = c₁.val := val_succAbove_of_lt k c₁ (by omega)
    have hlt0 : k.succAbove c₀ < k := by
      rw [Fin.lt_def, e0]
      omega
    have hlt1 : k.succAbove c₁ < k := by
      rw [Fin.lt_def, e1]
      omega
    rw [e0, e1, if_pos hlt0, if_pos hlt1,
      if_neg (show ¬ k.val ≤ c₁.val by omega)] at hrankSum
    rw [e0, e1]
    have hf1 : c₀.val + 1 + (n + 2 - c₁.val) + 1
        = c₀.val + 1 + (n + 1 - c₁.val) + 1 + 1 := by omega
    rw [hf1]
    have hmul : (c₀.val + 1 + (n + 1 - c₁.val) + 1 + 1) * (c₁.val + 1 - c₀.val)
        = (c₀.val + 1 + (n + 1 - c₁.val) + 1) * (c₁.val + 1 - c₀.val)
          + (c₁.val + 1 - c₀.val) := by ring
    rw [hmul]
    omega

/-- **Termwise sign identity, right family.** -/
theorem cutExp_succAbove_cutV {n : ℕ} (k : Fin (n + 2)) {c₀ c₁ : Fin (n + 1)} (h : c₀ < c₁)
    (hk0 : c₀.val < k.val) (hk1 : k.val ≤ c₁.val) :
    (k.val + cutExp ({c₀, c₁} : Finset (Fin (n + 1)))) % 2
      = ((cutU ({k.succAbove c₀, k.succAbove c₁} : Finset (Fin (n + 2)))).card - 1
          + cutExp ({k.succAbove c₀, k.succAbove c₁} : Finset (Fin (n + 2)))
          + cutRank (cutV ({k.succAbove c₀, k.succAbove c₁} : Finset (Fin (n + 2)))) k) % 2 := by
  have hlt : c₀.val < c₁.val := h
  have hc₁ : c₁.val < n + 1 := c₁.isLt
  have hT : k.succAbove c₀ < k.succAbove c₁ := succAbove_lt_succAbove k h
  have e0 : (k.succAbove c₀).val = c₀.val := val_succAbove_of_lt k c₀ (by omega)
  have e1 : (k.succAbove c₁).val = c₁.val + 1 := val_succAbove_of_ge k c₁ hk1
  rw [cutExp_pair h, cutExp_pair hT, card_cutU_pair hT, cutRank_cutV_pair hT k, e0, e1,
    if_pos (show k.val ≤ c₁.val + 1 by omega)]
  have hf1 : c₀.val + 1 + (n + 2 - (c₁.val + 1)) = c₀.val + 1 + (n + 1 - c₁.val) := by omega
  have hf2 : c₁.val + 1 + 1 - c₀.val = (c₁.val + 1 - c₀.val) + 1 := by omega
  rw [hf1, hf2]
  have hmul : (c₀.val + 1 + (n + 1 - c₁.val) + 1) * ((c₁.val + 1 - c₀.val) + 1)
      = (c₀.val + 1 + (n + 1 - c₁.val) + 1) * (c₁.val + 1 - c₀.val)
        + (c₀.val + 1 + (n + 1 - c₁.val) + 1) := by ring
  have hp : c₀.val * (c₁.val + 1) = c₀.val * c₁.val + c₀.val := by ring
  rw [hmul, hp]
  omega

end CharClass
end GroupApproximation
