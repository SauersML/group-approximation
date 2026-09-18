import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InvolRestrictHomeo
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidSplitSupport
import GroupApproximation.Meta.AxiomGuard

/-!
# Involution normal form, part 3: centralisers split along moved sets

Lane `sk-flip-12`, corollary (infrastructure for census row `2e7c7d9ab149`; no printed tex
sentence of its own).

Statements.
* `split_of_invariant_clopen`: if `h ∈ [[T]]` and `U` is a clopen set with `h '' U = U`, then
  `h = h₁ * h₂` with `h₁, h₂ ∈ [[T]]`, `h₁` supported in `U` and `h₂` supported in `Uᶜ`.
* `centralizer_split` (lane statement): if `T` is aperiodic and `f, h ∈ [[T]]` commute, then
  `h = h₁ * h₂` with `h₁, h₂ ∈ [[T]]`, `h₁` supported in `movedSet f`, `h₂` supported in
  `(movedSet f)ᶜ`.  The lane sketch leaves the hypotheses implicit; aperiodicity of `T` (implied by
  the Cantor-minimal package through `isAperiodic_of_isMinimalHomeo`) is what makes `movedSet f`
  clopen (`isClopen_movedSet`), and `f ∈ [[T]]` is needed for the same reason.

Proofs.
* Split: `h₁ := restrictToClopen h U`, `h₂ := restrictToClopen h Uᶜ` (`Uᶜ` is clopen and
  `h '' Uᶜ = Uᶜ`).  For `x ∈ U`: `h₂ x = x`, `h₁ x = h x`.  For `x ∉ U`: `h₂ x = h x ∉ U`, so
  `h₁ (h x) = h x`.
* Invariance: `h f = f h` gives `f (h x) = h (f x)`, and `h (f x) ≠ h x ↔ f x ≠ x` by injectivity,
  so `h x ∈ movedSet f ↔ x ∈ movedSet f`, i.e. `h '' movedSet f = movedSet f`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- An element of `[[T]]` preserving a clopen set splits as a product of its restrictions to the
set and to its complement. -/
theorem split_of_invariant_clopen {T h : X ≃ₜ X} (hh : h ∈ topologicalFullGroup T) {U : Set X}
    (hU : IsClopen U) (hinv : h '' U = U) :
    ∃ h₁ ∈ topologicalFullGroup T, ∃ h₂ ∈ topologicalFullGroup T,
      SupportedIn h₁ U ∧ SupportedIn h₂ Uᶜ ∧ h = h₁ * h₂ := by
  have hmaps : ∀ x, h x ∈ U ↔ x ∈ U := mem_iff_apply_mem_of_image_eq h hinv
  have hinvc : h '' Uᶜ = Uᶜ := by
    refine image_eq_of_forall_apply_mem_iff h fun x => ?_
    rw [Set.mem_compl_iff, Set.mem_compl_iff]
    exact not_congr (hmaps x)
  refine ⟨restrictToClopen h hU hinv, restrictToClopen_mem hh hU hinv,
    restrictToClopen h hU.compl hinvc, restrictToClopen_mem hh hU.compl hinvc,
    restrictToClopen_supportedIn h hU hinv, restrictToClopen_supportedIn h hU.compl hinvc, ?_⟩
  refine Homeomorph.ext fun x => ?_
  rw [Homeomorph.mul_apply]
  by_cases hx : x ∈ U
  · have hxc : x ∉ Uᶜ := fun h' => h' hx
    rw [restrictToClopen_supportedIn h hU.compl hinvc x hxc,
      restrictToClopen_apply_of_mem h hU hinv hx]
  · have hxc : x ∈ Uᶜ := hx
    have hhx : h x ∉ U := fun h' => hx ((hmaps x).1 h')
    rw [restrictToClopen_apply_of_mem h hU.compl hinvc hxc,
      restrictToClopen_supportedIn h hU hinv (h x) hhx]

/-- A homeomorphism commuting with `f` preserves the moved set of `f`. -/
theorem image_movedSet_eq_of_commute {h f : X ≃ₜ X} (hcomm : h * f = f * h) :
    h '' movedSet f = movedSet f := by
  have hc : ∀ x, h (f x) = f (h x) := fun x => by
    have h1 : (h * f) x = (f * h) x := congrArg (fun g : X ≃ₜ X => g x) hcomm
    rwa [Homeomorph.mul_apply, Homeomorph.mul_apply] at h1
  refine image_eq_of_forall_apply_mem_iff h fun x => ?_
  show f (h x) ≠ h x ↔ f x ≠ x
  rw [← hc x]
  constructor
  · intro hne heq
    exact hne (by rw [heq])
  · intro hne heq
    exact hne (h.injective heq)

/-- **Lane sk-flip-12, corollary.**  For aperiodic `T`, an element `h ∈ [[T]]` commuting with
`f ∈ [[T]]` splits as `h = h₁ * h₂` with `h₁, h₂ ∈ [[T]]`, `h₁` supported in `movedSet f` and
`h₂` supported in its complement. -/
theorem centralizer_split {T h f : X ≃ₜ X} (hT : IsAperiodic T)
    (hh : h ∈ topologicalFullGroup T) (hf : f ∈ topologicalFullGroup T) (hcomm : h * f = f * h) :
    ∃ h₁ ∈ topologicalFullGroup T, ∃ h₂ ∈ topologicalFullGroup T,
      SupportedIn h₁ (movedSet f) ∧ SupportedIn h₂ (movedSet f)ᶜ ∧ h = h₁ * h₂ :=
  split_of_invariant_clopen hh (isClopen_movedSet hT hf) (image_movedSet_eq_of_commute hcomm)

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.split_of_invariant_clopen
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.image_movedSet_eq_of_commute
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.centralizer_split
