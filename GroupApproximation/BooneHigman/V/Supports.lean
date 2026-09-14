import GroupApproximation.BooneHigman.V.ConeSwap
import GroupApproximation.GroupTheory.HydeLodha.HigmanEpstein

/-!
# Supports and conjugation of cone actions

The Higman–Epstein simplicity criterion of `GroupTheory/HydeLodha/HigmanEpstein.lean` sees permutations only
through their supports (`HydeLodha.SupportedIn`).  This module records the supports of the basic elements of
`V_d` and how actions inside cones conjugate and nest:

* `localize_supportedIn`: `localize w g` is supported in `cone w`;
* `coneSwap_supportedIn`: a cone swap is supported in the union of its two cones;
* `commute_localize`: actions inside incomparable cones commute;
* `MapsCone.conj_localize`: if `f` carries `cone w` onto `cone v` by prefix substitution, then
  `f * localize w g * f⁻¹ = localize v g`;
* `localize_append`: acting inside the cone of `v ++ w` is acting inside the cone of `v` by the action inside
  the cone of `w`.
-/

namespace GroupApproximation
namespace BooneHigman

open HydeLodha

variable {X : Type*}

theorem localize_supportedIn (w : List X) (g : Equiv.Perm (Cantor X)) :
    SupportedIn (localize w g) (cone w) :=
  fun _ hx ↦ localize_apply_of_not hx g

theorem coneSwap_supportedIn {v w : List X} (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) :
    SupportedIn (coneSwap v w hvw hwv) (cone v ∪ cone w) :=
  fun _ hx ↦ coneSwapFun_of_not (fun h ↦ hx (Or.inl h)) (fun h ↦ hx (Or.inr h))

/-- Actions inside incomparable cones commute. -/
theorem commute_localize {v w : List X} (hvw : ¬ v <+: w) (hwv : ¬ w <+: v)
    (g h : Equiv.Perm (Cantor X)) : Commute (localize v g) (localize w h) :=
  commute_of_supportedIn (localize_supportedIn v g) (localize_supportedIn w h)
    (disjoint_cone hvw hwv)

/-- Conjugating an action inside a cone by a prefix substitution between cones transports it. -/
theorem MapsCone.conj_localize {f : Equiv.Perm (Cantor X)} {w v : List X} (hf : MapsCone f w v)
    (g : Equiv.Perm (Cantor X)) : f * localize w g * f⁻¹ = localize v g := by
  refine Equiv.ext fun x ↦ ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  by_cases hx : IsStreamPrefix v x
  · obtain ⟨y, rfl⟩ := mem_cone_iff.mp hx
    have h1 : f⁻¹ (prepend v y) = prepend w y := hf.inv y
    rw [h1, localize_apply_prepend w g y, hf (g y), localize_apply_prepend v g y]
  · have h2 : f (f⁻¹ x) = x := f.apply_symm_apply x
    have hx' : ¬ IsStreamPrefix w (f⁻¹ x) := by
      intro h
      obtain ⟨y, hy⟩ := mem_cone_iff.mp h
      apply hx
      have hfx : x = prepend v y := by
        rw [← h2, hy, hf y]
      rw [hfx]
      exact isStreamPrefix_prepend v y
    rw [localize_apply_of_not hx' g, h2, localize_apply_of_not hx g]

/-- Acting inside the cone of `v ++ w` is acting inside the cone of `v` by the action inside the cone of
`w`. -/
theorem localize_append (v w : List X) (g : Equiv.Perm (Cantor X)) :
    localize (v ++ w) g = localize v (localize w g) := by
  refine Equiv.ext fun x ↦ ?_
  by_cases hv : IsStreamPrefix v x
  · obtain ⟨y, rfl⟩ := mem_cone_iff.mp hv
    rw [localize_apply_prepend v (localize w g) y]
    by_cases hw : IsStreamPrefix w y
    · obtain ⟨z, rfl⟩ := mem_cone_iff.mp hw
      rw [← prepend_append, localize_apply_prepend (v ++ w) g z,
        localize_apply_prepend w g z, prepend_append]
    · have hvw : ¬ IsStreamPrefix (v ++ w) (prepend v y) := by
        intro h
        apply hw
        obtain ⟨z, hz⟩ := mem_cone_iff.mp h
        rw [prepend_append] at hz
        rw [prepend_injective v hz]
        exact isStreamPrefix_prepend w z
      rw [localize_apply_of_not hvw g, localize_apply_of_not hw g]
  · have hvw : ¬ IsStreamPrefix (v ++ w) x :=
      fun h ↦ hv (IsStreamPrefix.of_prefix (List.prefix_append v w) h)
    rw [localize_apply_of_not hvw g, localize_apply_of_not hv (localize w g)]

end BooneHigman
end GroupApproximation
