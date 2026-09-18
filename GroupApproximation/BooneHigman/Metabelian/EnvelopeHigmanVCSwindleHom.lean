import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCCommonPush
import GroupApproximation.Meta.AxiomGuard

/-!
# Prefix lifts of the all-swaps free group (lane bh-hig-02)

For a word `c` over `Fin d`, the prefix lift `higSw_lift c` of the all-swaps free group sends
the letter `(x, y)` to `(c x, c y)`.  It carries the standard relators `higmanVC_rels d` into
themselves (`higSw_lift_rels`), and on the boundary it acts as the localization of the
evaluation to the cone of `c` (`higSw_perm_lift`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Incomparability is invariant under a common prefix. -/
theorem higSw_nprefix {X : Type*} (c : List X) {u v : List X} (h : ¬ u <+: v) :
    ¬ c ++ u <+: c ++ v := by
  rwa [List.prefix_append_right_inj]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_nprefix

/-- Incomparability of `c u` and `c v` is incomparability of `u` and `v`. -/
theorem higSw_incomp_iff {X : Type*} (c u v : List X) :
    (¬ c ++ u <+: c ++ v ∧ ¬ c ++ v <+: c ++ u) ↔ (¬ u <+: v ∧ ¬ v <+: u) := by
  simp only [List.prefix_append_right_inj]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_incomp_iff

/-- A stream `c z` beginning with `c u` has `z` beginning with `u`. -/
theorem higSw_isStreamPrefix_of_append {X : Type*} {c u : List X} {z : Cantor X}
    (h : IsStreamPrefix (c ++ u) (prepend c z)) : IsStreamPrefix u z := by
  obtain ⟨y, hy⟩ := mem_cone_iff.mp (mem_cone.mpr h)
  rw [prepend_append] at hy
  rw [prepend_injective c hy]
  exact isStreamPrefix_prepend u y

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_isStreamPrefix_of_append

/-- The cone swap of `c p`, `c q` on `c z` is `c` followed by the cone swap of `p`, `q` on
`z`. -/
theorem higSw_coneSwapFun_prepend {X : Type*} (c : List X) {p q : List X} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (z : Cantor X) :
    coneSwapFun (c ++ p) (c ++ q) (prepend c z) = prepend c (coneSwapFun p q z) := by
  by_cases hp : IsStreamPrefix p z
  · obtain ⟨y, rfl⟩ := mem_cone_iff.mp (mem_cone.mpr hp)
    rw [← prepend_append c p y, coneSwapFun_prepend_left, coneSwapFun_prepend_left,
      prepend_append c q y]
  · by_cases hq : IsStreamPrefix q z
    · obtain ⟨y, rfl⟩ := mem_cone_iff.mp (mem_cone.mpr hq)
      rw [← prepend_append c q y,
        coneSwapFun_prepend_right (higSw_nprefix c hpq) (higSw_nprefix c hqp),
        coneSwapFun_prepend_right hpq hqp, prepend_append c p y]
    · have hp' : ¬ IsStreamPrefix (c ++ p) (prepend c z) := fun h =>
        hp (higSw_isStreamPrefix_of_append h)
      have hq' : ¬ IsStreamPrefix (c ++ q) (prepend c z) := fun h =>
        hq (higSw_isStreamPrefix_of_append h)
      rw [coneSwapFun_of_not hp' hq', coneSwapFun_of_not hp hq]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_coneSwapFun_prepend

/-- Prefix substitutions of a cone swap lift to the cone swap of the lifted words. -/
theorem higSw_mapsCone {X : Type*} (c : List X) {p q x x' : List X} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (h : MapsCone (coneSwap p q hpq hqp) x x') :
    MapsCone (coneSwap (c ++ p) (c ++ q) (higSw_nprefix c hpq) (higSw_nprefix c hqp))
      (c ++ x) (c ++ x') := by
  intro y
  rw [coneSwap_apply, prepend_append c x y, higSw_coneSwapFun_prepend c hpq hqp,
    ← coneSwap_apply hpq hqp, h y, prepend_append c x' y]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_mapsCone

/-- The cone swap of `c p`, `c q` is the localization to the cone of `c` of the cone swap of
`p`, `q`. -/
theorem higSw_coneSwap_eq_localize {X : Type*} (c : List X) {p q : List X} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) :
    coneSwap (c ++ p) (c ++ q) (higSw_nprefix c hpq) (higSw_nprefix c hqp) =
      localize c (coneSwap p q hpq hqp) := by
  refine Equiv.ext fun z => ?_
  by_cases hz : IsStreamPrefix c z
  · obtain ⟨u, rfl⟩ := mem_cone_iff.mp (mem_cone.mpr hz)
    rw [localize_apply_prepend, coneSwap_apply, coneSwap_apply]
    exact higSw_coneSwapFun_prepend c hpq hqp u
  · have hp : ¬ IsStreamPrefix (c ++ p) z := fun h =>
      hz (IsStreamPrefix.of_prefix (List.prefix_append c p) h)
    have hq : ¬ IsStreamPrefix (c ++ q) z := fun h =>
      hz (IsStreamPrefix.of_prefix (List.prefix_append c q) h)
    rw [localize_apply_of_not hz, coneSwap_apply]
    exact coneSwapFun_of_not hp hq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_coneSwap_eq_localize

/-- The generator `(c x, c y)` of `V_d` is the localization to `c` of the generator `(x, y)`. -/
theorem higSw_swapOrOne_localize {d : ℕ} (c x y : List (Fin d)) :
    ((vgenSwapOrOne (c ++ x) (c ++ y) : ↥(higmanThompsonV (Fin d))) :
        Equiv.Perm (Cantor (Fin d))) =
      localize c ((vgenSwapOrOne x y : ↥(higmanThompsonV (Fin d))) :
        Equiv.Perm (Cantor (Fin d))) := by
  by_cases h : ¬ x <+: y ∧ ¬ y <+: x
  · rw [vgenSwapOrOne_eq h.1 h.2, vgenSwapOrOne_eq (higSw_nprefix c h.1) (higSw_nprefix c h.2)]
    exact higSw_coneSwap_eq_localize c h.1 h.2
  · have h' : ¬ (¬ c ++ x <+: c ++ y ∧ ¬ c ++ y <+: c ++ x) := fun h'' =>
      h ((higSw_incomp_iff c x y).mp h'')
    rw [higmanVFP_swapOrOne_of_not h, higmanVFP_swapOrOne_of_not h']
    exact (map_one (localize c)).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_swapOrOne_localize
