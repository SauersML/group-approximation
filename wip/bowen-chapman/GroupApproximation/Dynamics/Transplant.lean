import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Transplanting configuration maps to separating quotients

An exact pullback intertwining transfers injectivity to a quotient. A family
of quotient maps separating every finite set transfers surjectivity back to
the original configuration map: quotient preimages realize every finite
target pattern, giving a dense image, and continuity makes the image closed
when the alphabet is compact Hausdorff. Finite discrete alphabets are the
cellular-automaton specialization. No group structure is needed here.
-/

namespace GroupApproximation.Surjunctivity

universe uW uO uI uB

variable {W : Type uW} {O : Type uO} {I : Type uI} {B : Type uB}

/-- Pull a configuration back along a map of its coordinate sets. -/
def configPullback (π : W → O) (y : O → B) : W → B := y ∘ π

theorem configPullback_injective {π : W → O} (hπ : Function.Surjective π) :
    Function.Injective (configPullback (B := B) π) := by
  intro y z h
  funext o
  obtain ⟨w, rfl⟩ := hπ o
  exact congrFun h w

/-- Exact intertwining transfers injectivity to a surjective coordinate image. -/
theorem transplant_injective {π : W → O} (hπ : Function.Surjective π)
    {τ : (W → B) → (W → B)} {τO : (O → B) → (O → B)}
    (hinter : ∀ y, τ (configPullback π y) = configPullback π (τO y))
    (hτ : Function.Injective τ) : Function.Injective τO := by
  intro y z h
  apply configPullback_injective hπ
  apply hτ
  rw [hinter, hinter, h]

/-- Finite separation and quotient surjectivity realize any finite target pattern. -/
theorem transplant_finitePattern {Ω : I → Type uO}
    (π : ∀ i, W → Ω i) (hπ : ∀ i, Function.Surjective (π i))
    (τ : (W → B) → (W → B)) (τΩ : ∀ i, (Ω i → B) → (Ω i → B))
    (hinter : ∀ i y, τ (configPullback (π i) y) = configPullback (π i) (τΩ i y))
    (hsep : ∀ F : Finset W, ∃ i, Set.InjOn (π i) (F : Set W))
    (honto : ∀ i, Function.Surjective (τΩ i)) (F : Finset W) (z : W → B) :
    ∃ x : W → B, ∀ w ∈ F, τ x w = z w := by
  classical
  obtain ⟨i, hi⟩ := hsep F
  let f : F → Ω i := fun w ↦ π i w
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (hi a.property b.property hab)
  let d : Ω i → B := fun o ↦ z (Function.surjInv (hπ i) o)
  let zΩ : Ω i → B := Function.extend f (fun w : F ↦ z w) d
  have hzΩ (w : W) (hw : w ∈ F) : zΩ (π i w) = z w :=
    hf.extend_apply (fun w : F ↦ z w) d ⟨w, hw⟩
  obtain ⟨y, hy⟩ := honto i zΩ
  refine ⟨configPullback (π i) y, ?_⟩
  intro w hw
  rw [hinter, hy]
  exact hzΩ w hw

/-- Agreement with every finite target pattern makes a product-space image dense. -/
theorem denseRange_of_finitePatterns [TopologicalSpace B]
    {τ : (W → B) → (W → B)}
    (hpattern : ∀ (F : Finset W) (z : W → B),
      ∃ x : W → B, ∀ w ∈ F, τ x w = z w) : DenseRange τ := by
  intro z
  rw [mem_closure_iff]
  intro o ho hz
  obtain ⟨F, u, hu, hsub⟩ := isOpen_pi_iff.mp ho z hz
  obtain ⟨x, hx⟩ := hpattern F z
  refine ⟨τ x, hsub ?_, ⟨x, rfl⟩⟩
  intro w hw
  rw [hx w hw]
  exact (hu w hw).2

/-- Compactness closes the dense image supplied by finite target patterns. -/
theorem surjective_of_finitePatterns [TopologicalSpace B] [CompactSpace B] [T2Space B]
    {τ : (W → B) → (W → B)} (hτ : Continuous τ)
    (hpattern : ∀ (F : Finset W) (z : W → B),
      ∃ x : W → B, ∀ w ∈ F, τ x w = z w) : Function.Surjective τ := by
  have hclosed : IsClosed (Set.range τ) := (isCompact_range hτ).isClosed
  intro z
  have hz := denseRange_of_finitePatterns hpattern z
  rwa [hclosed.closure_eq] at hz

/-- Surjectivity on a finite-set-separating quotient family implies surjectivity. -/
theorem transplant_surjective [TopologicalSpace B] [CompactSpace B] [T2Space B]
    {Ω : I → Type uO} (π : ∀ i, W → Ω i)
    (hπ : ∀ i, Function.Surjective (π i))
    (τ : (W → B) → (W → B)) (τΩ : ∀ i, (Ω i → B) → (Ω i → B))
    (hτ : Continuous τ)
    (hinter : ∀ i y, τ (configPullback (π i) y) = configPullback (π i) (τΩ i y))
    (hsep : ∀ F : Finset W, ∃ i, Set.InjOn (π i) (F : Set W))
    (honto : ∀ i, Function.Surjective (τΩ i)) : Function.Surjective τ :=
  surjective_of_finitePatterns hτ (transplant_finitePattern π hπ τ τΩ hinter hsep honto)

/-- The finite discrete alphabet specialization, allowing empty alphabets. -/
theorem transplant_surjective_finite [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    {Ω : I → Type uO} (π : ∀ i, W → Ω i)
    (hπ : ∀ i, Function.Surjective (π i))
    (τ : (W → B) → (W → B)) (τΩ : ∀ i, (Ω i → B) → (Ω i → B))
    (hτ : Continuous τ)
    (hinter : ∀ i y, τ (configPullback (π i) y) = configPullback (π i) (τΩ i y))
    (hsep : ∀ F : Finset W, ∃ i, Set.InjOn (π i) (F : Set W))
    (honto : ∀ i, Function.Surjective (τΩ i)) : Function.Surjective τ :=
  transplant_surjective π hπ τ τΩ hτ hinter hsep honto

end GroupApproximation.Surjunctivity
