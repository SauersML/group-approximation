import GroupApproximation.BooneHigman.V.ConeSwap
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import GroupApproximation.Meta.AxiomGuard

/-!
# Counting leaves of a prefix substitution

Word-level facts about prefix substitutions `f` of the Cantor space, used to show that the cone
swaps generate `V_d` (`EnvelopeHigmanVSwapGenAll.lean`).

* `swapGen_exists_source`: if every word of length `N` has a target, every stream lies in some
  target cone.
* `swapGen_source_eq_of_prefix`: two sources of the same length whose targets are comparable
  coincide.
* `swapGen_length_eq_of_le`: if every word of length `N` has a target of length `≥ N`, all these
  targets have length exactly `N` (a pigeonhole count over the finitely many words of length `N`).
* `swapGen_inv_ge`: if every target has length `≤ N`, then `f⁻¹` has depth `N` with targets of
  length `≥ N`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*}

/-- Equal streams with prefixes `v` and `u` agree at every common position. -/
theorem swapGen_getElem_eq {v u : List X} {a b : Cantor X} (h : prepend v a = prepend u b)
    {k : ℕ} (hv : k < v.length) (hu : k < u.length) : v[k] = u[k] := by
  have hc := congrFun h k
  rwa [prepend_getElem v a hv, prepend_getElem u b hu] at hc

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_getElem_eq

/-- Every stream lies in a target cone of a depth-`N` prefix substitution. -/
theorem swapGen_exists_source {f : Equiv.Perm (Cantor X)} {N : ℕ}
    (hf : ∀ w : List X, w.length = N → ∃ v, MapsCone f w v) (z : Cantor X) :
    ∃ w v y, w.length = N ∧ MapsCone f w v ∧ prepend v y = z := by
  obtain ⟨v, hv⟩ := hf (firstWord N (f⁻¹ z)) (length_firstWord N _)
  refine ⟨firstWord N (f⁻¹ z), v, dropN N (f⁻¹ z), length_firstWord N _, hv, ?_⟩
  rw [← hv (dropN N (f⁻¹ z)), prepend_firstWord]
  exact f.apply_symm_apply z

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_exists_source

/-- Equal streams with long enough prefixes `v` and `u` have `v.take N = u.take N`. -/
theorem swapGen_take_eq_of_prepend_eq {v u : List X} {a b : Cantor X}
    (h : prepend v a = prepend u b) {N : ℕ} (hv : N ≤ v.length) (hu : N ≤ u.length) :
    v.take N = u.take N := by
  apply List.ext_getElem
  · rw [List.length_take, List.length_take]
    omega
  · intro k hk1 _
    have hk : k < N := lt_of_lt_of_le hk1 (List.length_take_le N v)
    rw [List.getElem_take, List.getElem_take]
    exact swapGen_getElem_eq h (by omega) (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_take_eq_of_prepend_eq

/-- Two sources of the same length with comparable targets coincide. -/
theorem swapGen_source_eq_of_prefix [Nontrivial X] {f : Equiv.Perm (Cantor X)}
    {w₁ w₂ v₁ v₂ : List X} (h₁ : MapsCone f w₁ v₁) (h₂ : MapsCone f w₂ v₂)
    (hlen : w₁.length = w₂.length) (hpre : v₁ <+: v₂) : w₁ = w₂ := by
  obtain ⟨a, -, -⟩ := exists_pair_ne X
  obtain ⟨t, rfl⟩ := hpre
  have key : prepend w₂ (fun _ => a) = prepend w₁ (prepend t (fun _ => a)) := by
    apply f.injective
    rw [h₂ (fun _ => a), h₁ (prepend t (fun _ => a)), prepend_append]
  exact ((prefix_of_prepend_eq key hlen.symm.le).eq_of_length hlen.symm).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_source_eq_of_prefix
