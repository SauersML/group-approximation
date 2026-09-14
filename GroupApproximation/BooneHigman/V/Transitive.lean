import GroupApproximation.BooneHigman.V.ConeSwap

/-!
# `V_d` moves any nonempty cone onto any other

Over an alphabet with at least two letters, `higmanThompsonV X` carries the cone of any nonempty word onto the
cone of any other nonempty word by a prefix substitution (`exists_mapsCone_of_ne_nil`).  Words with different
first letters are incomparable and a single cone swap does it; words with the same first letter are both
incomparable with a one-letter word `[z]`, and two cone swaps pass through `cone [z]`.
-/

namespace GroupApproximation
namespace BooneHigman

variable {X : Type*}

/-- Words with different first letters are incomparable. -/
theorem not_prefix_cons_of_ne {a b : X} (h : a ≠ b) (l₁ l₂ : List X) : ¬ (a :: l₁) <+: (b :: l₂) :=
  fun hp ↦ h (List.cons_prefix_cons.mp hp).1

/-- `V_d` carries any nonempty cone onto any other nonempty cone by a prefix substitution. -/
theorem exists_mapsCone_of_ne_nil [Finite X] [Nontrivial X] {v w : List X} (hv : v ≠ [])
    (hw : w ≠ []) : ∃ f ∈ higmanThompsonV X, MapsCone f v w := by
  obtain ⟨x, v', rfl⟩ := List.exists_cons_of_ne_nil hv
  obtain ⟨y, w', rfl⟩ := List.exists_cons_of_ne_nil hw
  by_cases hxy : x = y
  · subst hxy
    obtain ⟨z, hz⟩ := exists_ne x
    have h1 : ¬ (x :: v') <+: [z] := not_prefix_cons_of_ne hz.symm v' []
    have h2 : ¬ [z] <+: (x :: v') := not_prefix_cons_of_ne hz [] v'
    have h3 : ¬ [z] <+: (x :: w') := not_prefix_cons_of_ne hz [] w'
    have h4 : ¬ (x :: w') <+: [z] := not_prefix_cons_of_ne hz.symm w' []
    refine ⟨coneSwap [z] (x :: w') h3 h4 * coneSwap (x :: v') [z] h1 h2,
      (higmanThompsonV X).mul_mem (coneSwap_mem_higmanThompsonV h3 h4)
        (coneSwap_mem_higmanThompsonV h1 h2), ?_⟩
    exact (mapsCone_coneSwap_left h1 h2).comp (mapsCone_coneSwap_left h3 h4)
  · exact ⟨coneSwap (x :: v') (y :: w') (not_prefix_cons_of_ne hxy v' w')
      (not_prefix_cons_of_ne (Ne.symm hxy) w' v'), coneSwap_mem_higmanThompsonV _ _,
      mapsCone_coneSwap_left _ _⟩

end BooneHigman
end GroupApproximation
