import GroupApproximation.CuTensor.CuZModelRank

/-!
# The model of `Cu(𝒵)` is a Cu-semigroup

The monoid `ℕ ⊔ (0,∞]` of `CuZModel` satisfies the axioms O1–O4 of a Cu-semigroup.  The way-below
relation is read off from the rank: a class of strictly smaller rank is way below, a class way
below a soft class `t` has rank below `t`, and a compact class is way below every class above it.

## Main results

* `CuZModel.wayBelow_of_rank_lt`, `CuZModel.rank_lt_of_wayBelow_soft`;
* `CuZModel.exists_wayBelow_seq` (O2), `CuZModel.wayBelow_add` (O3),
  `CuZModel.isLUB_range_add` (O4);
* `CuZModel.isCuSemigroup`: the model is a Cu-semigroup;
* `CuZModel.rankHom`: the rank as an additive map to `ℝ≥0∞`.
-/

open scoped ENNReal

namespace GroupApproximation
namespace CuTensor
namespace CuZModel

/-- A soft class is way below every soft class of strictly larger rank. -/
theorem soft_wayBelow_soft_of_lt {s t : ℝ≥0∞} {hs : 0 < s} {ht : 0 < t} (h : s < t) :
    WayBelow (soft s hs) (soft t ht) := by
  intro f _ S hS htS
  by_contra hno
  have hub : soft s hs ∈ upperBounds (Set.range f) := by
    rintro _ ⟨n, rfl⟩
    exact (le_total' (soft s hs) (f n)).resolve_left fun hle => hno ⟨n, hle⟩
  exact absurd (soft_le_soft.1 (le_trans htS (hS.2 hub))) (not_le.2 h)

/-- A soft class is the supremum of a strictly increasing sequence of soft classes below it. -/
theorem exists_seq_isLUB_soft (t : ℝ≥0∞) (ht : 0 < t) :
    ∃ u : ℕ → ℝ≥0∞, ∃ hu : ∀ n, 0 < u n, StrictMono u ∧ (∀ n, u n < t) ∧
      IsLUB (Set.range fun n => soft (u n) (hu n)) (soft t ht) := by
  obtain ⟨u, hu, hmem, htend⟩ := exists_seq_strictMono_tendsto' ht
  have hlub : IsLUB (Set.range u) t := isLUB_of_tendsto_atTop hu.monotone htend
  refine ⟨u, fun n => (hmem n).1, hu, fun n => (hmem n).2, ?_, fun b hb => soft_le_iff.2 (hlub.2 ?_)⟩
  · rintro _ ⟨n, rfl⟩
    exact soft_le_soft.2 (hmem n).2.le
  · rintro _ ⟨n, rfl⟩
    exact soft_le_iff.1 (hb (Set.mem_range_self n))

/-- A class way below the soft class `t` has rank below `t`. -/
theorem rank_lt_of_wayBelow_soft {x : CuZModel} {t : ℝ≥0∞} {ht : 0 < t}
    (h : WayBelow x (soft t ht)) : rank x < t := by
  obtain ⟨u, hu, hmono, hlt, hlub⟩ := exists_seq_isLUB_soft t ht
  obtain ⟨n, hn⟩ := h (fun n => soft (u n) (hu n))
    (fun i j hij => soft_le_soft.2 (hmono.monotone hij)) (soft t ht) hlub le_rfl
  exact lt_of_le_of_lt (rank_mono hn) (hlt n)

/-- A class way below another class has finite rank. -/
theorem rank_ne_top_of_wayBelow {x y : CuZModel} (h : WayBelow x y) : rank x ≠ ∞ := by
  cases y with
  | cpt m => exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top m) (rank_mono h.le)
  | soft t ht => exact ne_top_of_lt (rank_lt_of_wayBelow_soft h)

/-- A class of strictly smaller rank is way below. -/
theorem wayBelow_of_rank_lt {x y : CuZModel} (h : rank x < rank y) : WayBelow x y := by
  cases y with
  | cpt n => exact WayBelow.of_le_left (le_of_rank_lt h) (isCompactElem_cpt n)
  | soft t ht =>
    cases x with
    | cpt m =>
      exact WayBelow.of_le_right (show WayBelow (cpt m) (cpt m) from isCompactElem_cpt m)
        (le_of_rank_lt h)
    | soft s hs => exact soft_wayBelow_soft_of_lt h

/-- **(O2) Every class is the supremum of a rapidly increasing sequence.** -/
theorem exists_wayBelow_seq (x : CuZModel) :
    ∃ f : ℕ → CuZModel, (∀ n, WayBelow (f n) (f (n + 1))) ∧ IsLUB (Set.range f) x := by
  cases x with
  | cpt n => exact ⟨fun _ => cpt n, fun _ => isCompactElem_cpt n, isLUB_range_const _⟩
  | soft t ht =>
    obtain ⟨u, hu, hmono, _, hlub⟩ := exists_seq_isLUB_soft t ht
    exact ⟨fun n => soft (u n) (hu n),
      fun n => soft_wayBelow_soft_of_lt (hmono (Nat.lt_add_one n)), hlub⟩

/-- **(O3) `≪` is compatible with addition.** -/
theorem wayBelow_add {x y x' y' : CuZModel} (h : WayBelow x y) (h' : WayBelow x' y') :
    WayBelow (x + x') (y + y') := by
  cases y with
  | soft t ht =>
    refine wayBelow_of_rank_lt ?_
    rw [rank_add, rank_add]
    exact ENNReal.add_lt_add_of_lt_of_le (rank_ne_top_of_wayBelow h')
      (rank_lt_of_wayBelow_soft h) (rank_mono h'.le)
  | cpt c =>
    cases y' with
    | soft t ht =>
      refine wayBelow_of_rank_lt ?_
      rw [rank_add, rank_add]
      exact ENNReal.add_lt_add_of_le_of_lt (rank_ne_top_of_wayBelow h) (rank_mono h.le)
        (rank_lt_of_wayBelow_soft h')
    | cpt d =>
      rw [cpt_add_cpt]
      refine WayBelow.of_le_left ?_ (isCompactElem_cpt (c + d))
      rw [← cpt_add_cpt]
      exact add_mono h.le h'.le

/-- **(O4) Suprema of increasing sequences are additive.** -/
theorem isLUB_range_add {f g : ℕ → CuZModel} (hf : Monotone f) (hg : Monotone g)
    {s t : CuZModel} (hs : IsLUB (Set.range f) s) (ht : IsLUB (Set.range g) t) :
    IsLUB (Set.range fun n => f n + g n) (s + t) := by
  refine ⟨?_, fun b hb => ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact add_mono (hs.1 (Set.mem_range_self n)) (ht.1 (Set.mem_range_self n))
  have hb' : ∀ n, f n + g n ≤ b := fun n => hb (Set.mem_range_self n)
  have hrank : rank s + rank t ≤ rank b := by
    rw [rank_eq_iSup hs, rank_eq_iSup ht,
      ENNReal.iSup_add_iSup_of_monotone (f := fun n => rank (f n)) (g := fun n => rank (g n))
        (fun a c hac => rank_mono (hf hac)) (fun a c hac => rank_mono (hg hac))]
    exact iSup_le fun n => (rank_add (f n) (g n)).symm.le.trans (rank_mono (hb' n))
  cases s with
  | soft v hv =>
    rw [soft_add, soft_le_iff]
    exact hrank
  | cpt c =>
    cases t with
    | soft w hw =>
      rw [add_soft, soft_le_iff]
      exact hrank
    | cpt d =>
      obtain ⟨k, hk⟩ := isCompactElem_cpt c f hf _ hs le_rfl
      obtain ⟨j, hj⟩ := isCompactElem_cpt d g hg _ ht le_rfl
      exact le_trans (add_mono (le_trans hk (hf (le_max_left k j)))
        (le_trans hj (hg (le_max_right k j)))) (hb' (max k j))

/-- **The model `ℕ ⊔ (0,∞]` is a Cu-semigroup.** -/
theorem isCuSemigroup : IsCuSemigroup CuZModel where
  zero_le := cpt_zero_le
  add_le_add := add_mono
  exists_isLUB := fun f _ => exists_isLUB_range f
  exists_wayBelow_seq := exists_wayBelow_seq
  wayBelow_add := wayBelow_add
  isLUB_add := isLUB_range_add

/-- The rank as an additive map to `ℝ≥0∞`. -/
def rankHom : CuZModel →+ ℝ≥0∞ where
  toFun := rank
  map_zero' := by
    show ((0 : ℕ) : ℝ≥0∞) = 0
    exact Nat.cast_zero
  map_add' := rank_add

@[simp] theorem rankHom_apply (x : CuZModel) : rankHom x = rank x := rfl

end CuZModel

end CuTensor
end GroupApproximation
