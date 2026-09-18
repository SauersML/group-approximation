import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Extending families adapted to a finite-dimensional linear map

Linear-algebra ingredient of `binaryLeavitt_idempotent_dichotomy`
(manuscript `simple_kazhdan_sofic_group.tex`, l.733-735, `sec:questions`,
question Q2).

Let `κ : V →ₗ[k] W` with `W` finite-dimensional, and let `X ⊆ V`.  Any finite
family `w` in `X` whose image under `κ` is linearly independent extends to a
finite family `w'` in `X` with three properties: it contains every `w j`, its
image under `κ` is still linearly independent, and `κ '' X` lies in the span
of that image.
-/

namespace GroupApproximation.Full.LVLowKZeroCore

theorem exists_adapted_extension_aux {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W] (κ : V →ₗ[k] W) (X : Set V) (n : ℕ) :
    ∀ (r : ℕ) (w : Fin r → V), Module.finrank k W - r ≤ n → (∀ j, w j ∈ X) →
      LinearIndependent k (κ ∘ w) →
      ∃ (r' : ℕ) (w' : Fin r' → V), (∀ j, w' j ∈ X) ∧ (∀ j, ∃ j', w' j' = w j) ∧
        LinearIndependent k (κ ∘ w') ∧
        ∀ x ∈ X, κ x ∈ Submodule.span k (Set.range (κ ∘ w')) := by
  induction n with
  | zero =>
      intro r w hr hwX hw
      refine ⟨r, w, hwX, fun j => ⟨j, rfl⟩, hw, ?_⟩
      intro x _
      by_contra hκx
      have hli : LinearIndependent k (κ ∘ (Fin.cons x w : Fin (r + 1) → V)) := by
        rw [Fin.comp_cons]
        exact hw.finCons hκx
      have hcard := hli.fintype_card_le_finrank
      rw [Fintype.card_fin] at hcard
      omega
  | succ n ih =>
      intro r w hr hwX hw
      by_cases hall : ∀ x ∈ X, κ x ∈ Submodule.span k (Set.range (κ ∘ w))
      · exact ⟨r, w, hwX, fun j => ⟨j, rfl⟩, hw, hall⟩
      · obtain ⟨x, hx, hκx⟩ :
            ∃ x ∈ X, κ x ∉ Submodule.span k (Set.range (κ ∘ w)) := by
          by_contra hne
          exact hall fun x hx => Classical.byContradiction fun hκx => hne ⟨x, hx, hκx⟩
        have hli : LinearIndependent k (κ ∘ (Fin.cons x w : Fin (r + 1) → V)) := by
          rw [Fin.comp_cons]
          exact hw.finCons hκx
        have hcX : ∀ j, (Fin.cons x w : Fin (r + 1) → V) j ∈ X := by
          intro j
          induction j using Fin.cases with
          | zero =>
              rw [Fin.cons_zero]
              exact hx
          | succ i =>
              rw [Fin.cons_succ]
              exact hwX i
        obtain ⟨r', w', hw'X, hsub, hli', hspan⟩ :=
          ih (r + 1) (Fin.cons x w) (by omega) hcX hli
        refine ⟨r', w', hw'X, fun j => ?_, hli', hspan⟩
        obtain ⟨j', hj'⟩ := hsub j.succ
        exact ⟨j', by rw [hj', Fin.cons_succ]⟩

/-- **Adapted extension.**  A family in `X` that is independent modulo `κ`
extends to a family in `X` that is independent modulo `κ` and whose image
spans `κ '' X`. -/
theorem exists_adapted_extension {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W] (κ : V →ₗ[k] W) (X : Set V)
    {r : ℕ} (w : Fin r → V) (hwX : ∀ j, w j ∈ X) (hw : LinearIndependent k (κ ∘ w)) :
    ∃ (r' : ℕ) (w' : Fin r' → V), (∀ j, w' j ∈ X) ∧ (∀ j, ∃ j', w' j' = w j) ∧
      LinearIndependent k (κ ∘ w') ∧
      ∀ x ∈ X, κ x ∈ Submodule.span k (Set.range (κ ∘ w')) :=
  exists_adapted_extension_aux κ X (Module.finrank k W - r) r w le_rfl hwX hw

end GroupApproximation.Full.LVLowKZeroCore
