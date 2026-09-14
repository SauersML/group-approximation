import GroupApproximation.BooneHigman.V.ConeSwap

/-!
# Model tests for `higmanThompsonV`

The depth definition of `V_d` is neither vacuous nor everything:

* positive model: the swap of the cones `[0]` and `[1]` is a nontrivial element of `V_2`;
* negative model: the transposition of the two constant streams is a permutation of the boundary that is not
  in `V_2`, because a prefix substitution on the cone of `0^N` cannot send the stream `0^∞` to `1^∞`.
-/

namespace GroupApproximation
namespace BooneHigman

theorem not_prefix_zero_one : ¬ ([0] : List (Fin 2)) <+: [1] :=
  fun h ↦ absurd (h.eq_of_length rfl) (by decide)

theorem not_prefix_one_zero : ¬ ([1] : List (Fin 2)) <+: [0] :=
  fun h ↦ absurd (h.eq_of_length rfl) (by decide)

/-- Positive model: the swap of the cones `[0]` and `[1]` lies in `V_2`. -/
theorem coneSwap_zero_one_mem :
    coneSwap ([0] : List (Fin 2)) [1] not_prefix_zero_one not_prefix_one_zero ∈
      higmanThompsonV (Fin 2) :=
  coneSwap_mem_higmanThompsonV not_prefix_zero_one not_prefix_one_zero

/-- Positive model: the swap of the cones `[0]` and `[1]` is not the identity. -/
theorem coneSwap_zero_one_ne_one :
    coneSwap ([0] : List (Fin 2)) [1] not_prefix_zero_one not_prefix_one_zero ≠ 1 := by
  intro h
  have h1 : coneSwap ([0] : List (Fin 2)) [1] not_prefix_zero_one not_prefix_one_zero
      (prepend [0] fun _ ↦ 0) = (1 : Equiv.Perm (Cantor (Fin 2))) (prepend [0] fun _ ↦ 0) := by
    rw [h]
  rw [coneSwap_apply, coneSwapFun_prepend_left, Equiv.Perm.one_apply] at h1
  have h2 := congrFun h1 0
  rw [prepend_getElem _ _ (by decide), prepend_getElem _ _ (by decide)] at h2
  exact absurd h2 (by decide)

open Classical in
/-- Negative model: the transposition of the constant streams `0^∞` and `1^∞` is not in `V_2`. -/
theorem swap_constant_streams_not_mem :
    Equiv.swap (fun _ : ℕ ↦ (0 : Fin 2)) (fun _ ↦ 1) ∉ higmanThompsonV (Fin 2) := by
  rintro ⟨N, hN⟩
  obtain ⟨v, hv⟩ := hN (firstWord N fun _ ↦ 0) (length_firstWord N _)
  have h1 := hv (dropN N fun _ ↦ 0)
  rw [prepend_firstWord, Equiv.swap_apply_left] at h1
  have h2 := congrFun h1 v.length
  rw [prepend_of_length_le _ _ (lt_irrefl _)] at h2
  have h3 : (1 : Fin 2) = 0 := h2
  exact absurd h3 (by decide)

end BooneHigman
end GroupApproximation
