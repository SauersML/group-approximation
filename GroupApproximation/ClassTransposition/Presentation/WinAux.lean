import GroupApproximation.ClassTransposition.Presentation.RelFC
import GroupApproximation.ClassTransposition.Presentation.ListBlock

/-!
# Window relations in `H P`: moving and stabilizing words

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §3).

A window relation involves only boxes near one position. When its lowest box is `≥ 2` it is the
shift (conjugate by `s`) of the same relation one box to the left (`eq_up`). When it stays away from
the tail it does not depend on the level (`eq_stable`). This file collects the bookkeeping for
the words of the window families: their shifts (`map_up_*`), positivity (`pos_*`), front
conditions (`frontW_*`) and levels (`levW_*`).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

theorem eq_up {n : ℕ} {u v : List Move} (hu : ∀ m ∈ u, m.Pos) (hv : ∀ m ∈ v, m.Pos)
    (h : toH P n u = toH P n v) : toH P (n + 1) (u.map Move.up) = toH P (n + 1) (v.map Move.up) := by
  rw [toH_up u hu, toH_up v hv, h]

theorem eq_stable {n : ℕ} {u v : List Move} (hu : FrontW n u) (hv : FrontW n v)
    (h : toH P n u = toH P n v) : toH P (n + 1) u = toH P (n + 1) v := by
  rw [toH_stable u n hu, toH_stable v n hv, h]

/-! ### Shifts -/

theorem map_up_swaps (k : ℕ) (w : List ℕ) : (swaps k w).map Move.up = swaps (k + 1) w := by
  simp only [swaps, List.map_map]
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, Move.up]
  congr 1
  omega

theorem map_up_layer (i p q : ℕ) : (layer i p q).map Move.up = layer (i + 1) p q := by
  simp only [layer, List.map_map]
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, Move.up]
  congr 1
  omega

theorem pos_swaps {k : ℕ} (hk : 1 ≤ k) (w : List ℕ) : ∀ m ∈ swaps k w, m.Pos := by
  intro m hm
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hm
  show 1 ≤ k + t
  omega

theorem pos_layer {i : ℕ} (hi : 1 ≤ i) (p q : ℕ) : ∀ m ∈ layer i p q, m.Pos := by
  intro m hm
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hm
  show 1 ≤ i + t * q
  omega

theorem pos_cons {m : Move} {w : List Move} (hm : m.Pos) (hw : ∀ m ∈ w, m.Pos) :
    ∀ m' ∈ m :: w, m'.Pos := by
  intro m' h
  rcases List.mem_cons.1 h with rfl | h
  · exact hm
  · exact hw m' h

theorem pos_append {u v : List Move} (hu : ∀ m ∈ u, m.Pos) (hv : ∀ m ∈ v, m.Pos) :
    ∀ m ∈ u ++ v, m.Pos := by
  intro m h
  rcases List.mem_append.1 h with h | h
  · exact hu m h
  · exact hv m h

/-! ### Front conditions and levels -/

theorem frontW_append : ∀ (n : ℕ) (u v : List Move),
    FrontW n (u ++ v) ↔ FrontW n u ∧ FrontW (levW n u) v
  | n, [], v => by simp [FrontW]
  | n, m :: u, v => by
    rw [List.cons_append]
    show m.Front n ∧ FrontW (m.lev n) (u ++ v) ↔ (m.Front n ∧ FrontW (m.lev n) u) ∧ _
    rw [frontW_append (m.lev n) u v, levW_cons, and_assoc]

theorem frontW_swaps (k L : ℕ) : ∀ w : List ℕ, (∀ t ∈ w, k + t + 2 < L) → FrontW L (swaps k w)
  | [], _ => trivial
  | t :: w, h => ⟨h t List.mem_cons_self, frontW_swaps k L w fun t' ht' =>
      h t' (List.mem_cons_of_mem _ ht')⟩

theorem levW_swaps (k L : ℕ) : ∀ w : List ℕ, levW L (swaps k w) = L
  | [] => rfl
  | _ :: w => levW_swaps k L w

theorem frontW_layer {q : ℕ} (hq : 1 ≤ q) : ∀ (p i L : ℕ), i + p < L → FrontW L (layer i p q)
  | 0, _, _, _ => trivial
  | p + 1, i, L, h => by
    rw [layer_succ]
    refine ⟨show i + 1 < L by omega, ?_⟩
    rw [lev_split q (by omega)]
    exact frontW_layer hq p (i + q) (L + q - 1) (by omega)

theorem levW_layer {q : ℕ} (hq : 1 ≤ q) : ∀ (p i L : ℕ), i + p ≤ L →
    levW L (layer i p q) = L + p * (q - 1)
  | 0, _, _, _ => by simp [layer]
  | p + 1, i, L, h => by
    rw [layer_succ, levW_cons, lev_split q (by omega),
      levW_layer hq p (i + q) (L + q - 1) (by omega), add_one_mul]
    omega

end GroupApproximation.ClassTransposition.Presentation
