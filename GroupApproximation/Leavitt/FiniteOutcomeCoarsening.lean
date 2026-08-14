import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Coarsening finite classical outcomes

A joint character measurement already has enough outcomes to encode an
entire response map.  Given a deterministic decoder from character outcomes
to maps, summing all atoms in one decoder fiber gives the map-outcome law.
This file records the finite scalar part of that operation.
-/

namespace GroupApproximation
namespace FiniteOutcomeCoarsening

noncomputable section

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]

/-- Push a finite weight through a deterministic decoder. -/
def pushforwardWeight (μ : X → ℝ) (decode : X → A) (a : A) : ℝ :=
  ∑ x ∈ (Finset.univ : Finset X).filter (fun x ↦ decode x = a), μ x

omit [Fintype A] in
theorem pushforwardWeight_nonnegative
    (μ : X → ℝ) (decode : X → A) (hμ : ∀ x, 0 ≤ μ x) :
    ∀ a, 0 ≤ pushforwardWeight μ decode a := by
  intro a
  exact Finset.sum_nonneg fun x _ ↦ hμ x

/-- Deterministic coarsening preserves total mass exactly. -/
theorem sum_pushforwardWeight
    (μ : X → ℝ) (decode : X → A) :
    ∑ a, pushforwardWeight μ decode a = ∑ x, μ x := by
  simpa [pushforwardWeight] using
    (Finset.sum_fiberwise (Finset.univ : Finset X) decode μ)

/-- A probability weight remains a probability weight after deterministic
coarsening. -/
theorem pushforwardWeight_isProbability
    (μ : X → ℝ) (decode : X → A)
    (hμnonneg : ∀ x, 0 ≤ μ x) (hμsum : ∑ x, μ x = 1) :
    (∀ a, 0 ≤ pushforwardWeight μ decode a) ∧
      ∑ a, pushforwardWeight μ decode a = 1 := by
  exact ⟨pushforwardWeight_nonnegative μ decode hμnonneg,
    (sum_pushforwardWeight μ decode).trans hμsum⟩

/-- Push a joint law through one deterministic decoder on each side. -/
def pushforwardPairWeight
    {Y B : Type*} [Fintype Y] [DecidableEq B]
    (μ : X → Y → ℝ) (decodeA : X → A) (decodeB : Y → B) :
    A → B → ℝ :=
  fun a b ↦ pushforwardWeight
    (fun p : X × Y ↦ μ p.1 p.2)
    (fun p : X × Y ↦ (decodeA p.1, decodeB p.2)) (a, b)

omit [Fintype A] in
theorem pushforwardPairWeight_nonnegative
    {Y B : Type*} [Fintype Y] [DecidableEq B]
    (μ : X → Y → ℝ) (decodeA : X → A) (decodeB : Y → B)
    (hμ : ∀ x y, 0 ≤ μ x y) :
    ∀ a b, 0 ≤ pushforwardPairWeight μ decodeA decodeB a b := by
  intro a b
  exact pushforwardWeight_nonnegative
    (fun p : X × Y ↦ μ p.1 p.2)
    (fun p : X × Y ↦ (decodeA p.1, decodeB p.2))
    (fun p ↦ hμ p.1 p.2) (a, b)

/-- Deterministic coarsening of a joint law preserves its total mass. -/
theorem sum_pushforwardPairWeight
    {Y B : Type*} [Fintype Y] [Fintype B] [DecidableEq B]
    (μ : X → Y → ℝ) (decodeA : X → A) (decodeB : Y → B) :
    ∑ a, ∑ b, pushforwardPairWeight μ decodeA decodeB a b =
      ∑ x, ∑ y, μ x y := by
  simpa only [pushforwardPairWeight, Fintype.sum_prod_type] using
    (sum_pushforwardWeight
    (fun p : X × Y ↦ μ p.1 p.2)
    (fun p : X × Y ↦ (decodeA p.1, decodeB p.2)))

/-- A joint probability law remains normalized after applying the two
deterministic decoders. -/
theorem pushforwardPairWeight_isProbability
    {Y B : Type*} [Fintype Y] [Fintype B] [DecidableEq B]
    (μ : X → Y → ℝ) (decodeA : X → A) (decodeB : Y → B)
    (hμnonneg : ∀ x y, 0 ≤ μ x y) (hμsum : ∑ x, ∑ y, μ x y = 1) :
    (∀ a b, 0 ≤ pushforwardPairWeight μ decodeA decodeB a b) ∧
      ∑ a, ∑ b, pushforwardPairWeight μ decodeA decodeB a b = 1 := by
  exact ⟨pushforwardPairWeight_nonnegative μ decodeA decodeB hμnonneg,
    (sum_pushforwardPairWeight μ decodeA decodeB).trans hμsum⟩

end
end FiniteOutcomeCoarsening
end GroupApproximation
