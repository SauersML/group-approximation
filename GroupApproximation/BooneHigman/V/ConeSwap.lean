import GroupApproximation.BooneHigman.V.Group

/-!
# Cone swaps in `V_d`

For incomparable words `v` and `w`, the cone swap exchanges `cone v` and `cone w` by the prefix substitutions
`v y ↦ w y` and `w y ↦ v y`, and fixes every other stream.  It is an involution of the boundary
(`coneSwapFun_involutive`) and an element of `higmanThompsonV X`, acting at depth `max |v| |w|`
(`coneSwap_hasDepth`).
-/

namespace GroupApproximation
namespace BooneHigman

variable {X : Type*}

open Classical in
/-- The map exchanging the cones of `v` and `w` by prefix substitution and fixing every other stream. -/
noncomputable def coneSwapFun (v w : List X) (x : Cantor X) : Cantor X :=
  if IsStreamPrefix v x then prepend w (dropN v.length x)
  else if IsStreamPrefix w x then prepend v (dropN w.length x) else x

section

variable {v w : List X}

theorem coneSwapFun_prepend_left (v w : List X) (y : Cantor X) :
    coneSwapFun v w (prepend v y) = prepend w y := by
  rw [coneSwapFun, if_pos (isStreamPrefix_prepend v y), dropN_prepend]

theorem coneSwapFun_prepend_right (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (y : Cantor X) :
    coneSwapFun v w (prepend w y) = prepend v y := by
  have hv : ¬ IsStreamPrefix v (prepend w y) := fun h ↦
    Set.disjoint_left.mp (disjoint_cone hvw hwv) h (prepend_mem_cone w y)
  rw [coneSwapFun, if_neg hv, if_pos (isStreamPrefix_prepend w y), dropN_prepend]

theorem coneSwapFun_of_not {x : Cantor X} (hv : ¬ IsStreamPrefix v x)
    (hw : ¬ IsStreamPrefix w x) : coneSwapFun v w x = x := by
  rw [coneSwapFun, if_neg hv, if_neg hw]

theorem coneSwapFun_involutive (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (x : Cantor X) :
    coneSwapFun v w (coneSwapFun v w x) = x := by
  by_cases hv : IsStreamPrefix v x
  · obtain ⟨y, rfl⟩ := mem_cone_iff.mp hv
    rw [coneSwapFun_prepend_left, coneSwapFun_prepend_right hvw hwv]
  · by_cases hw : IsStreamPrefix w x
    · obtain ⟨y, rfl⟩ := mem_cone_iff.mp hw
      rw [coneSwapFun_prepend_right hvw hwv, coneSwapFun_prepend_left]
    · rw [coneSwapFun_of_not hv hw, coneSwapFun_of_not hv hw]

/-- The cone swap of incomparable words `v` and `w`, as a permutation of the boundary. -/
noncomputable def coneSwap (v w : List X) (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) :
    Equiv.Perm (Cantor X) where
  toFun := coneSwapFun v w
  invFun := coneSwapFun v w
  left_inv := coneSwapFun_involutive hvw hwv
  right_inv := coneSwapFun_involutive hvw hwv

@[simp] theorem coneSwap_apply (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (x : Cantor X) :
    coneSwap v w hvw hwv x = coneSwapFun v w x := rfl

theorem coneSwap_mul_self (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) :
    coneSwap v w hvw hwv * coneSwap v w hvw hwv = 1 :=
  Equiv.ext fun x ↦ coneSwapFun_involutive hvw hwv x

theorem mapsCone_coneSwap_left (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) :
    MapsCone (coneSwap v w hvw hwv) v w :=
  coneSwapFun_prepend_left v w

theorem mapsCone_coneSwap_right (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) :
    MapsCone (coneSwap v w hvw hwv) w v :=
  coneSwapFun_prepend_right hvw hwv

/-- A cone swap acts as a prefix substitution at the depth of its longer word. -/
theorem coneSwap_hasDepth (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) :
    HasDepth (coneSwap v w hvw hwv) (max v.length w.length) := by
  intro u hu
  by_cases hvu : v <+: u
  · obtain ⟨r, rfl⟩ := hvu
    refine ⟨w ++ r, fun y ↦ ?_⟩
    rw [prepend_append, prepend_append]
    exact mapsCone_coneSwap_left hvw hwv (prepend r y)
  · by_cases hwu : w <+: u
    · obtain ⟨r, rfl⟩ := hwu
      refine ⟨v ++ r, fun y ↦ ?_⟩
      rw [prepend_append, prepend_append]
      exact mapsCone_coneSwap_right hvw hwv (prepend r y)
    · refine ⟨u, fun y ↦ coneSwapFun_of_not (fun hv ↦ hvu ?_) (fun hw ↦ hwu ?_)⟩
      · exact prefix_of_isStreamPrefix_of_length_le hv (isStreamPrefix_prepend u y)
          ((le_max_left _ _).trans_eq hu.symm)
      · exact prefix_of_isStreamPrefix_of_length_le hw (isStreamPrefix_prepend u y)
          ((le_max_right _ _).trans_eq hu.symm)

theorem coneSwap_mem_higmanThompsonV [Finite X] (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) :
    coneSwap v w hvw hwv ∈ higmanThompsonV X :=
  ⟨_, coneSwap_hasDepth hvw hwv⟩

end

end BooneHigman
end GroupApproximation
