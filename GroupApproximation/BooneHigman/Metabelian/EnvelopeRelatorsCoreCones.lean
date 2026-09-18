import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsFiniteStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite core relators: cone moves in `V_X`

Three facts about `V_X` used to shrink the disjoint-cone and splitting relator families of
`RNFree X H`.
* `rcore_mapsCone_coneSwap_fix`: a cone swap fixes pointwise every cone incomparable with
  both swapped words.
* `rcore_exists_to_root`: for incomparable words `u, w` there is `g ∈ V_X` carrying `cone u`
  onto `cone [x₀]` and `cone w` onto the cone of a word incomparable with `[x₀]`.
* `rcore_exists_stab_mapsCone`: for `x₁ ≠ x₀` and `w` incomparable with `[x₀]` there is
  `g ∈ V_X` fixing `cone [x₀]` pointwise and carrying `cone [x₁]` or `cone [x₁, x₁]` onto
  `cone w`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

variable {X : Type*}

theorem rcore_not_isStreamPrefix {v w : List X} (hvw : ¬ v <+: w) (hwv : ¬ w <+: v)
    (y : Cantor X) : ¬ IsStreamPrefix v (prepend w y) := fun h =>
  (prefix_or_prefix_of_isStreamPrefix h (isStreamPrefix_prepend w y)).elim hvw hwv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_not_isStreamPrefix

/-- A cone swap fixes every cone incomparable with both swapped words. -/
theorem rcore_mapsCone_coneSwap_fix {v t w : List X} (hvt : ¬ v <+: t) (htv : ¬ t <+: v)
    (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (htw : ¬ t <+: w) (hwt : ¬ w <+: t) :
    MapsCone (coneSwap v t hvt htv) w w := fun y => by
  rw [coneSwap_apply, coneSwapFun_of_not (rcore_not_isStreamPrefix hvw hwv y)
    (rcore_not_isStreamPrefix htw hwt y)]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_mapsCone_coneSwap_fix

theorem rcore_append_singleton_incomp {x y : X} (hxy : x ≠ y) (u : List X) :
    ¬ u ++ [x] <+: u ++ [y] := fun h =>
  hxy (List.cons_prefix_cons.mp ((List.prefix_append_right_inj u).mp h)).1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_append_singleton_incomp

/-- Swapping `cone v` with `cone [a]` carries a cone incomparable with `v` onto a cone
incomparable with `[a]`. -/
theorem rcore_swap_image {v w : List X} {a : X} (hva : ¬ v <+: [a]) (hav : ¬ [a] <+: v)
    (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) :
    ∃ w', MapsCone (coneSwap v [a] hva hav) w w' ∧ ¬ [a] <+: w' ∧ ¬ w' <+: [a] := by
  by_cases h1 : [a] <+: w
  · obtain ⟨t, rfl⟩ := h1
    refine ⟨v ++ t, (mapsCone_coneSwap_right hva hav).append t, fun h => ?_, fun h => ?_⟩
    · exact (List.prefix_or_prefix_of_prefix h (List.prefix_append v t)).elim hav hva
    · exact hva ((List.prefix_append v t).trans h)
  · by_cases h2 : w <+: [a]
    · exfalso
      rcases w with _ | ⟨c, t⟩
      · exact hwv List.nil_prefix
      · obtain ⟨rfl, ht⟩ := List.cons_prefix_cons.mp h2
        rw [List.prefix_nil.mp ht] at h1
        exact h1 List.prefix_rfl
    · exact ⟨w, rcore_mapsCone_coneSwap_fix hva hav hvw hwv h1 h2, h1, h2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_swap_image

/-- Move an incomparable pair `(u, w)` so that `u` lands on `[x₀]`. -/
theorem rcore_exists_to_root [Finite X] [Nontrivial X] (x₀ : X) {u w : List X}
    (huw : ¬ u <+: w) (hwu : ¬ w <+: u) :
    ∃ g ∈ higmanThompsonV X, MapsCone g u [x₀] ∧
      ∃ w', MapsCone g w w' ∧ ¬ [x₀] <+: w' ∧ ¬ w' <+: [x₀] := by
  rcases u with _ | ⟨b, u'⟩
  · exact absurd List.nil_prefix huw
  obtain ⟨a, hab⟩ := exists_ne b
  have hua : ¬ (b :: u') <+: [a] := fun h => hab (List.cons_prefix_cons.mp h).1.symm
  have hau : ¬ [a] <+: (b :: u') := fun h => hab (List.cons_prefix_cons.mp h).1
  obtain ⟨w₁, hw₁, hw₁a, haw₁⟩ := rcore_swap_image hua hau huw hwu
  by_cases hax : a = x₀
  · subst hax
    exact ⟨_, coneSwap_mem_higmanThompsonV hua hau, mapsCone_coneSwap_left hua hau, w₁, hw₁,
      hw₁a, haw₁⟩
  · have hax' : ¬ [a] <+: [x₀] := fun h => hax (List.cons_prefix_cons.mp h).1
    have hxa : ¬ [x₀] <+: [a] := fun h => hax (List.cons_prefix_cons.mp h).1.symm
    obtain ⟨w₂, hw₂, hw₂x, hxw₂⟩ := rcore_swap_image hax' hxa hw₁a haw₁
    exact ⟨_, (higmanThompsonV X).mul_mem (coneSwap_mem_higmanThompsonV hax' hxa)
      (coneSwap_mem_higmanThompsonV hua hau),
      (mapsCone_coneSwap_left hua hau).comp (mapsCone_coneSwap_left hax' hxa), w₂,
      hw₁.comp hw₂, hw₂x, hxw₂⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_exists_to_root

/-- For `x₁ ≠ x₀`, every cone incomparable with `[x₀]` is the image of `cone [x₁]` or of
`cone [x₁, x₁]` under an element of `V_X` fixing `cone [x₀]` pointwise. -/
theorem rcore_exists_stab_mapsCone [Finite X] {x₀ x₁ : X} (hne : x₁ ≠ x₀) {w : List X}
    (hxw : ¬ [x₀] <+: w) (hwx : ¬ w <+: [x₀]) :
    ∃ g ∈ higmanThompsonV X, MapsCone g [x₀] [x₀] ∧
      (MapsCone g [x₁] w ∨ MapsCone g [x₁, x₁] w) := by
  have h11x : ¬ [x₁, x₁] <+: [x₀] := fun h => hne (List.cons_prefix_cons.mp h).1
  have hx11 : ¬ [x₀] <+: [x₁, x₁] := fun h => hne (List.cons_prefix_cons.mp h).1.symm
  by_cases h1 : w <+: [x₁, x₁]
  · refine ⟨1, (higmanThompsonV X).one_mem, mapsCone_one _, ?_⟩
    rcases w with _ | ⟨c, t⟩
    · exact absurd List.nil_prefix hwx
    obtain ⟨rfl, ht⟩ := List.cons_prefix_cons.mp h1
    rcases t with _ | ⟨d, s⟩
    · exact Or.inl (mapsCone_one _)
    obtain ⟨rfl, hs⟩ := List.cons_prefix_cons.mp ht
    rw [List.prefix_nil.mp hs]
    exact Or.inr (mapsCone_one _)
  by_cases h2 : [x₁, x₁] <+: w
  · obtain ⟨t, ht⟩ := h2
    have hw : w = x₁ :: x₁ :: t := ht.symm
    subst hw
    have h10x : ¬ [x₁, x₀] <+: [x₀] := fun h => hne (List.cons_prefix_cons.mp h).1
    have hx10 : ¬ [x₀] <+: [x₁, x₀] := fun h => hne (List.cons_prefix_cons.mp h).1.symm
    have h1110 : ¬ [x₁, x₁] <+: [x₁, x₀] := fun h =>
      hne (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp h).2).1
    have h1011 : ¬ [x₁, x₀] <+: [x₁, x₁] := fun h =>
      hne (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp h).2).1.symm
    have h10w : ¬ [x₁, x₀] <+: x₁ :: x₁ :: t := fun h =>
      hne (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp h).2).1.symm
    have hw10 : ¬ (x₁ :: x₁ :: t) <+: [x₁, x₀] := fun h =>
      hne (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp h).2).1
    exact ⟨_, (higmanThompsonV X).mul_mem (coneSwap_mem_higmanThompsonV h10w hw10)
      (coneSwap_mem_higmanThompsonV h1110 h1011),
      (rcore_mapsCone_coneSwap_fix h1110 h1011 h11x hx11 h10x hx10).comp
        (rcore_mapsCone_coneSwap_fix h10w hw10 h10x hx10 hwx hxw),
      Or.inr ((mapsCone_coneSwap_left h1110 h1011).comp (mapsCone_coneSwap_left h10w hw10))⟩
  · exact ⟨_, coneSwap_mem_higmanThompsonV h2 h1,
      rcore_mapsCone_coneSwap_fix h2 h1 h11x hx11 hwx hxw,
      Or.inr (mapsCone_coneSwap_left h2 h1)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_exists_stab_mapsCone

end GroupApproximation.BooneHigman.Metabelian.Envelope
