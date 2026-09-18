import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveLooseCount
import GroupApproximation.Meta.AxiomGuard

/-!
# The open rotation sector as a list

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-20.

Write `σ` for the rotation.  Let `k > 0` be the first time `σ^k x = y`.  The open sector from `x`
to `y` is the list `σ x, σ² x, …, σ^(k-1) x` (`regionMoveLoose_sector`).

## Route

* `regionMoveLoose_mem_sector_iff`: a dart is on the list exactly when it is in
  `RotationBetween M x y`.
* `regionMoveLoose_sector_nodup`: the list has no repeated dart.  If `σ^i x = σ^j x` with
  `0 < i < j < k`, then `σ^(j-i)` fixes `x`, so `σ^(k-(j-i)) x = y` arrives before `k`.
* `regionMoveLoose_not_rotationBetween_self` and `regionMoveLoose_not_rotationBetween_end`: neither
  end of the sector lies inside it.

## Truth check

Proved lemmas.  They only use that `σ` is a permutation and that `k` is the first arrival.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

universe v

open scoped Classical

/-- **The open rotation sector** `σ x, …, σ^(k-1) x`. -/
def regionMoveLoose_sector (M : CombMap.{v}) (x : M.Dart) (k : ℕ) : List M.Dart :=
  (List.range' 1 (k - 1)).map fun i => (M.sigma ^ i) x

/-- **Rotation powers compose.** -/
theorem regionMoveLoose_pow_apply_add (M : CombMap.{v}) (x : M.Dart) (i j : ℕ) :
    (M.sigma ^ (i + j)) x = (M.sigma ^ i) ((M.sigma ^ j) x) := by
  rw [pow_add, Equiv.Perm.mul_apply]

/-- **No return before the first arrival**: for `0 < t < k`, `σ^t x ≠ x`. -/
theorem regionMoveLoose_pow_ne_self {M : CombMap.{v}} {x y : M.Dart} {k : ℕ}
    (hk : (M.sigma ^ k) x = y) (hmin : ∀ t, 0 < t → t < k → (M.sigma ^ t) x ≠ y)
    {t : ℕ} (ht : 0 < t) (htk : t < k) : (M.sigma ^ t) x ≠ x := by
  intro h
  apply hmin (k - t) (by omega) (by omega)
  have e : (M.sigma ^ k) x = (M.sigma ^ (k - t)) ((M.sigma ^ t) x) := by
    rw [← regionMoveLoose_pow_apply_add, Nat.sub_add_cancel htk.le]
  rw [← hk, e, h]

/-- **Equal powers differ by a fixing power.** -/
theorem regionMoveLoose_pow_sub_eq_self {M : CombMap.{v}} {x : M.Dart} {i j : ℕ}
    (hij : (M.sigma ^ i) x = (M.sigma ^ j) x) (h : i ≤ j) : (M.sigma ^ (j - i)) x = x := by
  apply (M.sigma ^ i).injective
  rw [← regionMoveLoose_pow_apply_add, Nat.add_sub_cancel' h, hij]

/-- **The sector list is the rotation sector.** -/
theorem regionMoveLoose_mem_sector_iff {M : CombMap.{v}} {x y : M.Dart} {k : ℕ} (hk0 : 0 < k)
    (hk : (M.sigma ^ k) x = y) (hmin : ∀ t, 0 < t → t < k → (M.sigma ^ t) x ≠ y)
    (z : M.Dart) : z ∈ regionMoveLoose_sector M x k ↔ RotationBetween M x y z := by
  unfold regionMoveLoose_sector RotationBetween
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.mem_range'_1] at hi
    exact ⟨i, by omega, rfl, fun b hb hbi => hmin b hb (by omega)⟩
  · rintro ⟨a, ha, rfl, hb⟩
    have hak : a < k := by
      by_contra hge
      exact hb k hk0 (by omega) hk
    exact ⟨a, List.mem_range'_1.mpr ⟨ha, by omega⟩, rfl⟩

/-- **The sector list has no repeated dart.** -/
theorem regionMoveLoose_sector_nodup {M : CombMap.{v}} {x y : M.Dart} {k : ℕ}
    (hk : (M.sigma ^ k) x = y) (hmin : ∀ t, 0 < t → t < k → (M.sigma ^ t) x ≠ y) :
    (regionMoveLoose_sector M x k).Nodup := by
  unfold regionMoveLoose_sector
  refine List.Nodup.map_on (fun i hi j hj hij => ?_) List.nodup_range'
  have hij' : (M.sigma ^ i) x = (M.sigma ^ j) x := hij
  rw [List.mem_range'_1] at hi hj
  rcases lt_trichotomy i j with h | h | h
  · exact absurd (regionMoveLoose_pow_sub_eq_self hij' h.le)
      (regionMoveLoose_pow_ne_self hk hmin (by omega) (by omega))
  · exact h
  · exact absurd (regionMoveLoose_pow_sub_eq_self hij'.symm h.le)
      (regionMoveLoose_pow_ne_self hk hmin (by omega) (by omega))

/-- **The start of a sector is not inside it.** -/
theorem regionMoveLoose_not_rotationBetween_self {M : CombMap.{v}} {x y : M.Dart} {k : ℕ}
    (hk0 : 0 < k) (hk : (M.sigma ^ k) x = y)
    (hmin : ∀ t, 0 < t → t < k → (M.sigma ^ t) x ≠ y) : ¬RotationBetween M x y x := by
  rintro ⟨a, ha, hax, hb⟩
  have hak : a < k := by
    by_contra hge
    exact hb k hk0 (by omega) hk
  exact regionMoveLoose_pow_ne_self hk hmin ha hak hax

/-- **The end of a sector is not inside it.** -/
theorem regionMoveLoose_not_rotationBetween_end {M : CombMap.{v}} {x y : M.Dart} :
    ¬RotationBetween M x y y := by
  rintro ⟨a, ha, hay, hb⟩
  exact hb a ha le_rfl hay

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_sector
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_pow_apply_add
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_pow_ne_self
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_pow_sub_eq_self
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_mem_sector_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_sector_nodup
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_not_rotationBetween_self
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_not_rotationBetween_end
