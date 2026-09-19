import Mathlib.Topology.Continuous

/-!
# Continuous images of closure points in closed targets
-/

namespace GroupApproximation

universe u v

/-- If a continuous map sends a set into a closed target, it sends every
point of the source closure into that target. -/
theorem continuous_image_closure_mem_closed
    {α : Type u} {β : Type v} [TopologicalSpace α] [TopologicalSpace β]
    (f : α → β) (hf : Continuous f) {s : Set α} {t : Set β}
    (hst : ∀ x ∈ s, f x ∈ t) (ht : IsClosed t) {x : α}
    (hx : x ∈ closure s) : f x ∈ t := by
  have himage : f x ∈ closure (f '' s) :=
    image_closure_subset_closure_image hf ⟨x, hx, rfl⟩
  exact closure_minimal (by
    rintro _ ⟨y, hy, rfl⟩
    exact hst y hy) ht himage

end GroupApproximation
