import GroupApproximation.CuTensor.CuZModelCu

/-!
# Recognising the Cuntz semigroup `ℕ ⊔ (0,∞]`

Let `S` be a Cu-semigroup with an additive rank `d : S → [0,∞]`.  Suppose that

* `d` is monotone;
* `d` sends compact elements injectively into `ℕ` and onto `ℕ`;
* `x ≪ y` with `y` not compact implies `d x < d y`;
* `d x < d y` implies `x ≤ y`;
* every `t ∈ (0,∞]` is the rank of a non-compact element.

Then `x ↦ cpt n` (for compact `x` with `d x = n`) and `x ↦ soft (d x)` (otherwise) is an additive
order isomorphism `S ≃o CuZModel`.  For a simple, stably finite, monotracial C*-algebra with strict
comparison, `K₀ = ℤ` and `[1] = 1`, these are the facts that identify its Cuntz semigroup with
`Cu(𝒵)`; this file proves the order-theoretic part.

## Main results

* `IsCuZLike`: the hypotheses above;
* `IsCuZLike.toModel_le_iff`, `IsCuZLike.toModel_add`, `IsCuZLike.toModel_surjective`;
* `IsCuZLike.exists_orderIso`: the additive order isomorphism with the model;
* `CuZModel.isCuZLike_rankHom`: the model itself satisfies the hypotheses.
-/

open scoped ENNReal

namespace GroupApproximation
namespace CuTensor

open CuZModel

variable {S : Type*} [PartialOrder S] [AddCommMonoid S]

/-- The hypotheses under which a Cu-semigroup with an additive rank `d` is `ℕ ⊔ (0,∞]`. -/
structure IsCuZLike (d : S →+ ℝ≥0∞) : Prop where
  /-- `S` is a Cu-semigroup. -/
  cu : IsCuSemigroup S
  /-- The rank is monotone. -/
  mono : Monotone d
  /-- Compact elements have natural ranks. -/
  exists_nat_of_compact : ∀ x : S, IsCompactElem x → ∃ n : ℕ, d x = n
  /-- Compact elements are determined by their ranks. -/
  eq_of_compact : ∀ x y : S, IsCompactElem x → IsCompactElem y → d x = d y → x = y
  /-- Every natural number is the rank of a compact element. -/
  exists_compact : ∀ n : ℕ, ∃ x : S, IsCompactElem x ∧ d x = n
  /-- Way below a non-compact element, the rank drops. -/
  lt_of_wayBelow : ∀ x y : S, WayBelow x y → ¬ IsCompactElem y → d x < d y
  /-- Strict comparison: a smaller rank lies below. -/
  le_of_lt : ∀ x y : S, d x < d y → x ≤ y
  /-- Every positive value is the rank of a non-compact element. -/
  exists_soft : ∀ t : ℝ≥0∞, 0 < t → ∃ x : S, ¬ IsCompactElem x ∧ d x = t

/-- Each term of a rapidly increasing sequence is way below its supremum. -/
theorem wayBelow_of_seq {T : Type*} [Preorder T] {f : ℕ → T}
    (hf : ∀ n, WayBelow (f n) (f (n + 1))) {x : T} (hlub : IsLUB (Set.range f) x) (n : ℕ) :
    WayBelow (f n) x :=
  (hf n).of_le_right (hlub.1 (Set.mem_range_self (n + 1)))

namespace IsCuZLike

variable {d : S →+ ℝ≥0∞}

/-- A non-compact element has positive rank. -/
theorem pos (h : IsCuZLike d) {x : S} (hx : ¬ IsCompactElem x) : 0 < d x := by
  obtain ⟨f, hf, hlub⟩ := h.cu.exists_wayBelow_seq x
  exact lt_of_le_of_lt zero_le (h.lt_of_wayBelow _ _ (wayBelow_of_seq hf hlub 0) hx)

/-- A non-compact element lies below every element of larger or equal rank. -/
theorem le_of_not_compact (h : IsCuZLike d) {x y : S} (hx : ¬ IsCompactElem x)
    (hxy : d x ≤ d y) : x ≤ y := by
  obtain ⟨f, hf, hlub⟩ := h.cu.exists_wayBelow_seq x
  refine hlub.2 ?_
  rintro _ ⟨n, rfl⟩
  exact h.le_of_lt _ _ (lt_of_lt_of_le (h.lt_of_wayBelow _ _ (wayBelow_of_seq hf hlub n) hx) hxy)

/-- A compact element below a non-compact element has strictly smaller rank. -/
theorem lt_of_le_of_compact (h : IsCuZLike d) {x y : S} (hx : IsCompactElem x)
    (hy : ¬ IsCompactElem y) (hxy : x ≤ y) : d x < d y :=
  h.lt_of_wayBelow _ _ (WayBelow.of_le_right (show WayBelow x x from hx) hxy) hy

/-- Compact elements are ordered by their ranks. -/
theorem le_of_compact (h : IsCuZLike d) {x y : S} (hx : IsCompactElem x)
    (hy : IsCompactElem y) (hxy : d x ≤ d y) : x ≤ y := by
  rcases hxy.lt_or_eq with hlt | heq
  · exact h.le_of_lt _ _ hlt
  · exact (h.eq_of_compact x y hx hy heq).le

/-- The sum of compact elements is compact. -/
theorem compact_add (h : IsCuZLike d) {x y : S} (hx : IsCompactElem x)
    (hy : IsCompactElem y) : IsCompactElem (x + y) :=
  h.cu.wayBelow_add (show WayBelow x x from hx) (show WayBelow y y from hy)

/-- Adding anything to a non-compact element gives a non-compact element. -/
theorem not_compact_add (h : IsCuZLike d) {x : S} (hx : ¬ IsCompactElem x) (y : S) :
    ¬ IsCompactElem (x + y) := by
  intro hc
  obtain ⟨f, hf, hlub⟩ := h.cu.exists_wayBelow_seq x
  have hmono : Monotone f := monotone_of_wayBelow_seq hf
  have hsum : IsLUB (Set.range fun n => f n + y) (x + y) :=
    h.cu.isLUB_add hmono monotone_const hlub (isLUB_range_const y)
  obtain ⟨n, hn⟩ := hc (fun n => f n + y)
    (fun i j hij => h.cu.add_le_add (hmono hij) le_rfl) (x + y) hsum le_rfl
  obtain ⟨k, hk⟩ := h.exists_nat_of_compact _ hc
  have hne : d x + d y ≠ ∞ := by
    rw [← map_add d x y, hk]
    exact ENNReal.natCast_ne_top k
  have hle : d x + d y ≤ d (f n) + d y :=
    (map_add d x y).symm.le.trans ((h.mono hn).trans (map_add d (f n) y).le)
  exact absurd ((ENNReal.add_le_add_iff_right (ENNReal.add_ne_top.1 hne).2).1 hle)
    (not_le.2 (h.lt_of_wayBelow _ _ (wayBelow_of_seq hf hlub n) hx))

/-- The comparison map to the model: a compact element of rank `n` goes to `cpt n`, and a
non-compact element `x` goes to `soft (d x)`. -/
noncomputable def toModel (h : IsCuZLike d) (x : S) : CuZModel := by
  classical
  exact if hx : IsCompactElem x then cpt (Classical.choose (h.exists_nat_of_compact x hx))
    else soft (d x) (h.pos hx)

theorem toModel_of_compact (h : IsCuZLike d) {x : S} (hx : IsCompactElem x) :
    ∃ n : ℕ, h.toModel x = cpt n ∧ d x = n := by
  refine ⟨Classical.choose (h.exists_nat_of_compact x hx), ?_,
    Classical.choose_spec (h.exists_nat_of_compact x hx)⟩
  rw [toModel, dif_pos hx]

theorem toModel_of_not_compact (h : IsCuZLike d) {x : S} (hx : ¬ IsCompactElem x) :
    h.toModel x = soft (d x) (h.pos hx) := by
  rw [toModel, dif_neg hx]

/-- The comparison map preserves rank. -/
theorem rank_toModel (h : IsCuZLike d) (x : S) : rank (h.toModel x) = d x := by
  by_cases hx : IsCompactElem x
  · obtain ⟨n, hn, hdn⟩ := h.toModel_of_compact hx
    rw [hn, rank_cpt, hdn]
  · rw [h.toModel_of_not_compact hx, rank_soft]

/-- **The comparison map is an order embedding.** -/
theorem toModel_le_iff (h : IsCuZLike d) (x y : S) : h.toModel x ≤ h.toModel y ↔ x ≤ y := by
  by_cases hx : IsCompactElem x
  · obtain ⟨m, hm, hdm⟩ := h.toModel_of_compact hx
    by_cases hy : IsCompactElem y
    · obtain ⟨n, hn, hdn⟩ := h.toModel_of_compact hy
      rw [hm, hn, cpt_le_cpt, ← Nat.cast_le (α := ℝ≥0∞), ← hdm, ← hdn]
      exact ⟨h.le_of_compact hx hy, fun hxy => h.mono hxy⟩
    · rw [hm, h.toModel_of_not_compact hy, cpt_le_soft, ← hdm]
      exact ⟨h.le_of_lt _ _, h.lt_of_le_of_compact hx hy⟩
  · rw [h.toModel_of_not_compact hx, soft_le_iff, h.rank_toModel]
    exact ⟨h.le_of_not_compact hx, fun hxy => h.mono hxy⟩

theorem toModel_injective (h : IsCuZLike d) : Function.Injective h.toModel := fun x y hxy =>
  le_antisymm ((h.toModel_le_iff x y).1 hxy.le) ((h.toModel_le_iff y x).1 hxy.ge)

/-- **The comparison map is onto the model.** -/
theorem toModel_surjective (h : IsCuZLike d) : Function.Surjective h.toModel := by
  intro z
  cases z with
  | cpt n =>
    obtain ⟨x, hx, hdx⟩ := h.exists_compact n
    obtain ⟨m, hm, hdm⟩ := h.toModel_of_compact hx
    refine ⟨x, ?_⟩
    rw [hm, Nat.cast_injective (hdm.symm.trans hdx)]
  | soft t ht =>
    obtain ⟨x, hx, hdx⟩ := h.exists_soft t ht
    exact ⟨x, (h.toModel_of_not_compact hx).trans (soft_congr hdx)⟩

theorem toModel_add_of_not_compact (h : IsCuZLike d) {x : S} (hx : ¬ IsCompactElem x) (y : S) :
    h.toModel (x + y) = h.toModel x + h.toModel y := by
  rw [h.toModel_of_not_compact hx, h.toModel_of_not_compact (h.not_compact_add hx y), soft_add]
  exact soft_congr (by rw [map_add, h.rank_toModel])

/-- **The comparison map is additive.** -/
theorem toModel_add (h : IsCuZLike d) (x y : S) :
    h.toModel (x + y) = h.toModel x + h.toModel y := by
  by_cases hx : IsCompactElem x
  · by_cases hy : IsCompactElem y
    · obtain ⟨m, hm, hdm⟩ := h.toModel_of_compact hx
      obtain ⟨n, hn, hdn⟩ := h.toModel_of_compact hy
      obtain ⟨k, hk, hdk⟩ := h.toModel_of_compact (h.compact_add hx hy)
      rw [hm, hn, hk, cpt_add_cpt]
      congr 1
      apply Nat.cast_injective (R := ℝ≥0∞)
      rw [Nat.cast_add, ← hdk, ← hdm, ← hdn, map_add]
    · rw [add_comm x y, h.toModel_add_of_not_compact hy, add_comm]
  · exact h.toModel_add_of_not_compact hx y

theorem toModel_zero (h : IsCuZLike d) : h.toModel 0 = 0 := by
  obtain ⟨n, hn, hdn⟩ := h.toModel_of_compact h.cu.isCompactElem_zero
  rw [hn, zero_def]
  congr 1
  apply Nat.cast_injective (R := ℝ≥0∞)
  rw [← hdn, map_zero, Nat.cast_zero]

/-- The comparison map as an order isomorphism. -/
noncomputable def orderIso (h : IsCuZLike d) : S ≃o CuZModel where
  toEquiv := Equiv.ofBijective h.toModel ⟨h.toModel_injective, h.toModel_surjective⟩
  map_rel_iff' := fun {a b} => h.toModel_le_iff a b

theorem orderIso_apply (h : IsCuZLike d) (x : S) : h.orderIso x = h.toModel x := rfl

/-- **Recognition theorem.** A Cu-semigroup satisfying `IsCuZLike d` is additively order
isomorphic to `ℕ ⊔ (0,∞]`, by an isomorphism that carries `d` to the rank. -/
theorem exists_orderIso (h : IsCuZLike d) :
    ∃ e : S ≃o CuZModel, (∀ x y, e (x + y) = e x + e y) ∧ e 0 = 0 ∧
      ∀ x, rank (e x) = d x :=
  ⟨h.orderIso, fun x y => h.toModel_add x y, h.toModel_zero, fun x => h.rank_toModel x⟩

end IsCuZLike

/-- **Model test.** The model `ℕ ⊔ (0,∞]` with its rank satisfies `IsCuZLike`. -/
theorem CuZModel.isCuZLike_rankHom : IsCuZLike CuZModel.rankHom where
  cu := CuZModel.isCuSemigroup
  mono := CuZModel.rank_mono
  exists_nat_of_compact := fun x hx => by
    obtain ⟨n, rfl⟩ := isCompactElem_iff.1 hx
    exact ⟨n, rfl⟩
  eq_of_compact := fun x y hx hy hxy => by
    obtain ⟨m, rfl⟩ := isCompactElem_iff.1 hx
    obtain ⟨n, rfl⟩ := isCompactElem_iff.1 hy
    have hmn : (m : ℝ≥0∞) = n := hxy
    rw [Nat.cast_injective hmn]
  exists_compact := fun n => ⟨cpt n, isCompactElem_cpt n, rfl⟩
  lt_of_wayBelow := fun x y hxy hy => by
    cases y with
    | cpt n => exact absurd (isCompactElem_cpt n) hy
    | soft t ht => exact rank_lt_of_wayBelow_soft hxy
  le_of_lt := fun _ _ hxy => le_of_rank_lt hxy
  exists_soft := fun t ht => ⟨soft t ht, not_isCompactElem_soft t ht, rfl⟩

end CuTensor
end GroupApproximation
