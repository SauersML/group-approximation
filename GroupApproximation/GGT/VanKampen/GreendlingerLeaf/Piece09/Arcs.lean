import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonFaceClass
import Mathlib.Data.List.Rotate
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 09: suffix arcs of a cyclic arc

For step 5 of the proof in `GreendlingerLeaf/Piece09/Walk.lean`: dropping the first `k` darts of a
cyclic arc leaves a cyclic arc of the same carrier, starting `k` positions later (modulo the length
of the carrier).

* `rotate_add_length`: rotating by `m + |l|` is rotating by `m`.
* `darts_eq_drop`: an arc whose rotated carrier is the rotated carrier of `T` rotated by `k`, with
  `k` fewer darts, lists the darts of `T` after the first `k`.
* `exists_suffixArc`: the suffix arc, with its start `T.start + k` when that stays in the carrier.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09

open GroupApproximation.GGT.VanKampen.Embedded

/-- Rotating by `m + |l|` is rotating by `m`. -/
theorem rotate_add_length {α : Type*} (l : List α) (m : ℕ) :
    l.rotate (m + l.length) = l.rotate m := by
  rw [← List.rotate_mod l (m + l.length), ← List.rotate_mod l m, Nat.add_mod_right]

/-- An arc rotated `k` further, with `k` fewer darts, lists the darts after the first `k`. -/
theorem darts_eq_drop {α : Type*} {cycle : List α} (T T' : CyclicArc cycle) (k : ℕ)
    (hk : k ≤ T.length) (hl : T'.length = T.length - k)
    (hrot : T'.rotated = T.rotated.rotate k) : T'.darts = T.darts.drop k := by
  have hTle := T.length_le
  have hR : k ≤ T.rotated.length := by
    rw [T.rotated_length]
    omega
  show T'.rotated.take T'.length = (T.rotated.take T.length).drop k
  rw [hrot, hl, List.drop_take, List.rotate_eq_drop_append_take hR,
    List.take_append_of_le_length]
  rw [List.length_drop, T.rotated_length]
  omega

/-- **The suffix arc.**  Dropping the first `k ≤ |T|` darts of a cyclic arc `T` leaves a cyclic arc of
the same carrier with `|T| - k` darts, starting at `T.start + k` when that stays in the carrier. -/
theorem exists_suffixArc {α : Type*} {cycle : List α} (T : CyclicArc cycle) (k : ℕ)
    (hk : k ≤ T.length) :
    ∃ T' : CyclicArc cycle, T'.length = T.length - k ∧ T'.darts = T.darts.drop k ∧
      (T.start.1 + k ≤ cycle.length → T'.start.1 = T.start.1 + k) := by
  have hTle := T.length_le
  have hs := T.start.isLt
  by_cases hc : T.start.1 + k ≤ cycle.length
  · obtain ⟨T', hT's, hT'l⟩ : ∃ T' : CyclicArc cycle,
        T'.start.1 = T.start.1 + k ∧ T'.length = T.length - k :=
      ⟨⟨⟨T.start.1 + k, by omega⟩, T.length - k, by omega⟩, rfl, rfl⟩
    have hrot : T'.rotated = T.rotated.rotate k := by
      rw [CyclicArc.rotated_eq_rotate, CyclicArc.rotated_eq_rotate, List.rotate_rotate, hT's]
    exact ⟨T', hT'l, darts_eq_drop T T' k hk hT'l hrot, fun _ => hT's⟩
  · obtain ⟨T', hT's, hT'l⟩ : ∃ T' : CyclicArc cycle,
        T'.start.1 + cycle.length = T.start.1 + k ∧ T'.length = T.length - k :=
      ⟨⟨⟨T.start.1 + k - cycle.length, by omega⟩, T.length - k, by omega⟩,
        show T.start.1 + k - cycle.length + cycle.length = T.start.1 + k by omega, rfl⟩
    have hrot : T'.rotated = T.rotated.rotate k := by
      rw [CyclicArc.rotated_eq_rotate, CyclicArc.rotated_eq_rotate, List.rotate_rotate, ← hT's,
        rotate_add_length]
    exact ⟨T', hT'l, darts_eq_drop T T' k hk hT'l hrot, fun h => absurd h hc⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.rotate_add_length
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.darts_eq_drop
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.exists_suffixArc
