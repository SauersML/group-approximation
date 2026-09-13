import GroupApproximation.CuTensor.CuZRecognition

/-!
# Axiom (O5) and the softness hypothesis of `IsCuZLike`

Axiom (O5), almost algebraic order, says that `x' ≪ x ≤ y` gives some `z` with
`x' + z ≤ y ≤ x + z`.  In a Cu-semigroup with (O5), a non-compact element leaves room way below it:
`x ≪ y` with `y` not compact gives a nonzero `z` with `x + z ≤ y`.  So a faithful rank that is finite
way below drops strictly way below a non-compact element, which is the field `lt_of_wayBelow` of
`IsCuZLike`.  Finiteness way below follows from a unit of finite rank whose multiples exhaust the
semigroup, as `[1]` does in a simple unital C*-algebra.

## Main results

* `CuO5`: axiom (O5);
* `IsCuSemigroup.exists_wayBelow_between`: interpolation for `≪`;
* `IsCuSemigroup.exists_ne_zero_add_le`: room below a non-compact element under (O5);
* `lt_of_wayBelow_of_cuO5`, `finite_of_unit`, `IsCuZLike.of_cuO5`;
* model tests `CuZModel.cuO5`, `CuZModel.rankHom_faithful`, `CuZModel.le_softTop`,
  `CuZModel.isLUB_nsmul_cpt_one`.
-/

open scoped ENNReal

namespace GroupApproximation
namespace CuTensor

/-- Axiom (O5), almost algebraic order: `x' ≪ x ≤ y` gives some `z` with `x' + z ≤ y ≤ x + z`. -/
def CuO5 (S : Type*) [PartialOrder S] [AddCommMonoid S] : Prop :=
  ∀ x' x y : S, WayBelow x' x → x ≤ y → ∃ z, x' + z ≤ y ∧ y ≤ x + z

namespace IsCuSemigroup

variable {S : Type*} [PartialOrder S] [AddCommMonoid S]

/-- Multiples of an element increase. -/
theorem monotone_nsmul (hS : IsCuSemigroup S) (u : S) : Monotone fun n : ℕ => n • u := by
  refine monotone_nat_of_le_succ fun n => ?_
  have h := hS.add_le_add (le_refl (n • u)) (hS.zero_le u)
  rw [add_zero, ← succ_nsmul] at h
  exact h

/-- **Interpolation.** `x ≪ y` gives some `y'` with `x ≪ y' ≪ y`. -/
theorem exists_wayBelow_between (hS : IsCuSemigroup S) {x y : S} (h : WayBelow x y) :
    ∃ y', WayBelow x y' ∧ WayBelow y' y := by
  obtain ⟨f, hf, hlub⟩ := hS.exists_wayBelow_seq y
  obtain ⟨n, hn⟩ := h f (monotone_of_wayBelow_seq hf) y hlub le_rfl
  exact ⟨f (n + 1), WayBelow.of_le_left hn (hf n), wayBelow_of_seq hf hlub (n + 1)⟩

/-- **Room below a non-compact element.** Under (O5), `x ≪ y` with `y` not compact gives a nonzero
`z` with `x + z ≤ y`. -/
theorem exists_ne_zero_add_le (hS : IsCuSemigroup S) (h5 : CuO5 S) {x y : S} (h : WayBelow x y)
    (hy : ¬ IsCompactElem y) : ∃ z, z ≠ 0 ∧ x + z ≤ y := by
  obtain ⟨y', hxy', hy'y⟩ := hS.exists_wayBelow_between h
  obtain ⟨z, hle, hge⟩ := h5 x y' y hxy' hy'y.le
  refine ⟨z, fun hz => hy ?_, hle⟩
  rw [hz, add_zero] at hge
  exact WayBelow.of_le_left hge hy'y

/-- An element way below an element under the supremum of the multiples of `u` lies below some
multiple of `u`. -/
theorem exists_le_nsmul_of_wayBelow (hS : IsCuSemigroup S) {u s x y : S}
    (hs : IsLUB (Set.range fun n : ℕ => n • u) s) (hys : y ≤ s) (h : WayBelow x y) :
    ∃ n : ℕ, x ≤ n • u :=
  h (fun n : ℕ => n • u) (hS.monotone_nsmul u) s hs hys

end IsCuSemigroup

section Rank

variable {S : Type*} [PartialOrder S] [AddCommMonoid S] {d : S →+ ℝ≥0∞}

/-- **The rank drops way below a non-compact element.** For a Cu-semigroup with (O5) and a
monotone, faithful rank that is finite way below, `x ≪ y` with `y` not compact gives `d x < d y`. -/
theorem lt_of_wayBelow_of_cuO5 (hS : IsCuSemigroup S) (h5 : CuO5 S) (hmono : Monotone d)
    (hfaithful : ∀ z, d z = 0 → z = 0) (hfinite : ∀ x y, WayBelow x y → d x ≠ ∞) {x y : S}
    (h : WayBelow x y) (hy : ¬ IsCompactElem y) : d x < d y := by
  obtain ⟨z, hz, hle⟩ := hS.exists_ne_zero_add_le h5 h hy
  calc d x < d x + d z := ENNReal.lt_add_right (hfinite x y h) fun h0 => hz (hfaithful z h0)
    _ = d (x + z) := (map_add d x z).symm
    _ ≤ d y := hmono hle

/-- **Finiteness way below from a unit.** If `d u ≠ ∞` and every element lies below the supremum
`s` of the multiples of `u`, then `d` is finite way below. -/
theorem finite_of_unit (hS : IsCuSemigroup S) (hmono : Monotone d) {u s : S} (hu : d u ≠ ∞)
    (hs : IsLUB (Set.range fun n : ℕ => n • u) s) (hfull : ∀ y, y ≤ s) (x y : S)
    (h : WayBelow x y) : d x ≠ ∞ := by
  obtain ⟨n, hn⟩ := hS.exists_le_nsmul_of_wayBelow hs (hfull y) h
  refine ne_top_of_le_ne_top ?_ (hmono hn)
  rw [map_nsmul, nsmul_eq_mul]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hu

/-- **Recognition from (O5).** `IsCuZLike d`, with the field `lt_of_wayBelow` replaced by (O5), a
faithful rank, and finiteness of the rank way below. -/
theorem IsCuZLike.of_cuO5 (hS : IsCuSemigroup S) (h5 : CuO5 S) (hmono : Monotone d)
    (hfaithful : ∀ z, d z = 0 → z = 0) (hfinite : ∀ x y, WayBelow x y → d x ≠ ∞)
    (hnat : ∀ x : S, IsCompactElem x → ∃ n : ℕ, d x = n)
    (heq : ∀ x y : S, IsCompactElem x → IsCompactElem y → d x = d y → x = y)
    (hcpt : ∀ n : ℕ, ∃ x : S, IsCompactElem x ∧ d x = n)
    (hlt : ∀ x y : S, d x < d y → x ≤ y)
    (hsoft : ∀ t : ℝ≥0∞, 0 < t → ∃ x : S, ¬ IsCompactElem x ∧ d x = t) :
    IsCuZLike d where
  cu := hS
  mono := hmono
  exists_nat_of_compact := hnat
  eq_of_compact := heq
  exists_compact := hcpt
  lt_of_wayBelow := fun _ _ h hy => lt_of_wayBelow_of_cuO5 hS h5 hmono hfaithful hfinite h hy
  le_of_lt := hlt
  exists_soft := hsoft

end Rank

namespace CuZModel

/-- **Model test.** The model satisfies (O5). -/
theorem cuO5 : CuO5 CuZModel := by
  intro x' x y hx'x hxy
  cases y with
  | soft c hc =>
    have hlt : rank x' < c := rank_lt_of_wayBelow_soft (WayBelow.of_le_right hx'x hxy)
    refine ⟨soft (c - rank x') (tsub_pos_of_lt hlt), ?_, ?_⟩
    · rw [add_soft]
      exact soft_le_iff.2 (add_tsub_cancel_of_le hlt.le).le
    · rw [soft_le_iff, rank_add, rank_soft]
      calc c = rank x' + (c - rank x') := (add_tsub_cancel_of_le hlt.le).symm
        _ ≤ rank x + (c - rank x') := add_le_add (rank_mono hx'x.le) le_rfl
  | cpt m =>
    cases x with
    | cpt k =>
      have hkm : k ≤ m := cpt_le_cpt.1 hxy
      refine ⟨cpt (m - k), ?_, ?_⟩
      · calc x' + cpt (m - k) ≤ cpt k + cpt (m - k) := add_mono hx'x.le le_rfl
          _ = cpt m := by rw [cpt_add_cpt, Nat.add_sub_of_le hkm]
      · rw [cpt_add_cpt]
        exact cpt_le_cpt.2 (Nat.add_sub_of_le hkm).ge
    | soft t ht =>
      have hlt : rank x' < t := rank_lt_of_wayBelow_soft hx'x
      have ham : rank x' < m := lt_of_lt_of_le hlt (soft_le_cpt.1 hxy)
      refine ⟨soft ((m : ℝ≥0∞) - rank x') (tsub_pos_of_lt ham), ?_, ?_⟩
      · rw [add_soft]
        exact soft_le_cpt.2 (add_tsub_cancel_of_le ham.le).le
      · refine le_of_rank_lt ?_
        rw [rank_add, rank_cpt, rank_soft, rank_soft]
        calc (m : ℝ≥0∞) = rank x' + ((m : ℝ≥0∞) - rank x') :=
              (add_tsub_cancel_of_le ham.le).symm
          _ < t + ((m : ℝ≥0∞) - rank x') :=
              ENNReal.add_lt_add_right (ENNReal.sub_ne_top (ENNReal.natCast_ne_top m)) hlt

/-- **Model test.** The rank of the model is faithful. -/
theorem rankHom_faithful (z : CuZModel) (hz : rankHom z = 0) : z = 0 := by
  cases z with
  | cpt n =>
    have hn : ((n : ℕ) : ℝ≥0∞) = 0 := hz
    rw [zero_def, Nat.cast_eq_zero.1 hn]
  | soft t ht => exact absurd (show t = 0 from hz) ht.ne'

theorem nsmul_cpt_one (n : ℕ) : n • cpt 1 = cpt n := by
  induction n with
  | zero => rw [zero_nsmul, zero_def]
  | succ n ih => rw [succ_nsmul, ih, cpt_add_cpt]

/-- The largest class of the model, the soft class of rank `∞`. -/
def softTop : CuZModel := soft ∞ (lt_of_lt_of_le zero_lt_one le_top)

/-- **Model test.** Every class lies below `softTop`. -/
theorem le_softTop (y : CuZModel) : y ≤ softTop := by
  cases y with
  | cpt n => exact cpt_le_soft.2 (ENNReal.natCast_lt_top n)
  | soft t ht => exact soft_le_soft.2 le_top

/-- **Model test.** `softTop` is the supremum of the multiples of `cpt 1`. -/
theorem isLUB_nsmul_cpt_one : IsLUB (Set.range fun n : ℕ => n • cpt 1) softTop := by
  refine ⟨?_, fun b hb => ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (nsmul_cpt_one n).trans_le (le_softTop (cpt n))
  · have htop : rank b = ∞ := by
      by_contra hne
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hne
      have hle : n • cpt 1 ≤ b := hb (Set.mem_range_self n)
      rw [nsmul_cpt_one] at hle
      exact absurd (rank_mono hle) (not_le.2 hn)
    exact soft_le_iff.2 htop.ge

end CuZModel

end CuTensor
end GroupApproximation
