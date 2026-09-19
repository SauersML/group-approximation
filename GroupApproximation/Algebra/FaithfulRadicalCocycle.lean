import GroupApproximation.Algebra.CoprodIAltWord
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.Tactic.Group

/-!
# A faithful commutator gate in a free product

For nonidentity elements `z : H` and `b : B`, the commutator of their images
in `H * B` is a reduced alternating word of length four.  Consequently it is
trivial exactly when `b` is trivial, and the resulting pointed map from `B`
is injective.

The proof is entirely algebraic.  This file deliberately does not mention a
particular residual: downstream residual theories only need to transport `z`
to the free product and use normality to retain the commutator.
-/

namespace GroupApproximation
namespace FaithfulRadicalCocycle

open Monoid Monoid.CoprodI
open scoped commutatorElement Monoid.Coprod

universe u

variable {H B : Type u} [Group H] [Group B]

/-- The minimal abstract interface used by the radical computer: a normal
subgroup assignment, functorial under every homomorphism.  The single-universe
form keeps the algebraic theorem lightweight; concrete residuals may live in
larger universes and can also use `gate_mem_normal` directly. -/
structure HomMonotoneRadical (u : Level) where
  radical : ∀ (G : Type u) [Group G], Subgroup G
  normal : ∀ (G : Type u) [Group G], (radical G).Normal
  map_le : ∀ {G K : Type u} [Group G] [Group K] (f : G →* K),
    (radical G).map f ≤ radical K

/-- The two free factors as a `Bool`-indexed family. -/
def factor (H B : Type u) [Group H] [Group B] : Bool → Type u
  | false => H
  | true => B

instance factorGroup (i : Bool) : Group (factor H B i) := by
  cases i <;> simp only [factor] <;> infer_instance

/-- The binary free product mapped to the indexed free product of its two
lifted factors. -/
def toIndexed : H ∗ B →* CoprodI (factor H B) :=
  Monoid.Coprod.lift
    (CoprodI.of (M := factor H B) (i := false))
    (CoprodI.of (M := factor H B) (i := true))

@[simp] theorem toIndexed_inl (h : H) :
    toIndexed (Monoid.Coprod.inl h : H ∗ B) =
      CoprodI.of (i := false) h := by
  simp [toIndexed]
  rfl

@[simp] theorem toIndexed_inr (b : B) :
    toIndexed (Monoid.Coprod.inr b : H ∗ B) =
      CoprodI.of (i := true) b := by
  simp [toIndexed]
  rfl

/-- The commutator gate based at `z`. -/
def gate (z : H) (b : B) : H ∗ B :=
  ⁅(Monoid.Coprod.inl z : H ∗ B), (Monoid.Coprod.inr b : H ∗ B)⁆

@[simp] theorem gate_one (z : H) : gate z (1 : B) = 1 := by
  simp [gate]

/-- A commutator gate based at an element of `N` belongs to `[N, ⊤]`. -/
theorem gate_mem_commutator (N : Subgroup (H ∗ B)) {z : H}
    (hz : Monoid.Coprod.inl z ∈ N) (b : B) :
    gate z b ∈ ⁅N, (⊤ : Subgroup (H ∗ B))⁆ := by
  have hb : (Monoid.Coprod.inr b : H ∗ B) ∈ (⊤ : Subgroup (H ∗ B)) :=
    Subgroup.mem_top _
  simpa [gate] using
    (Subgroup.commutator_mem_commutator hz hb)

/-- If `N` is normal, the gate based at an element of `N` remains in `N`. -/
theorem gate_mem_normal (N : Subgroup (H ∗ B)) [N.Normal] {z : H}
    (hz : Monoid.Coprod.inl z ∈ N) (b : B) : gate z b ∈ N := by
  exact (Subgroup.commutator_le_left
    (H₁ := N) (H₂ := (⊤ : Subgroup (H ∗ B)))) (gate_mem_commutator N hz b)

/-- Generic radical form of the gate-membership theorem. -/
theorem gate_mem_radical {H B : Type u} [Group H] [Group B]
    (R : HomMonotoneRadical u) {z : H} (hz : z ∈ R.radical H) (b : B) :
    gate z b ∈ R.radical (H ∗ B) := by
  letI : (R.radical (H ∗ B)).Normal := R.normal (H ∗ B)
  apply gate_mem_normal (R.radical (H ∗ B))
  apply R.map_le (Monoid.Coprod.inl : H →* H ∗ B)
  exact Subgroup.mem_map_of_mem _ hz

/-- A nontrivial control input gives a nontrivial reduced alternating
commutator. -/
theorem gate_ne_one {z : H} (hz : z ≠ 1) {b : B} (hb : b ≠ 1) :
    gate z b ≠ 1 := by
  classical
  let letters : List (Σ i, factor H B i) :=
    [⟨false, z⟩, ⟨true, b⟩, ⟨false, z⁻¹⟩, ⟨true, b⁻¹⟩]
  have hletters :
      (letters.map fun p ↦ CoprodI.of p.2).prod ≠
        (1 : CoprodI (factor H B)) := by
    refine CoprodIAltWord.listProd_ne_one (l := letters) (by simp [letters]) ?_ ?_
    · intro p hp
      simp only [letters, List.mem_cons] at hp
      rcases hp with rfl | hp
      · change z ≠ 1
        exact hz
      rcases hp with rfl | hp
      · change b ≠ 1
        exact hb
      rcases hp with rfl | hp
      · change z⁻¹ ≠ 1
        simpa only [inv_ne_one] using hz
      rcases hp with rfl | hp
      · change b⁻¹ ≠ 1
        simpa only [inv_ne_one] using hb
      · exact (List.not_mem_nil hp).elim
    · simp [letters]
  intro hgate
  apply hletters
  have hmapped := congrArg toIndexed hgate
  have hcomm :
      ⁅CoprodI.of (M := factor H B) (i := false) z,
        CoprodI.of (M := factor H B) (i := true) b⁆ = 1 := by
    simpa [gate] using hmapped
  calc
    (letters.map fun p ↦ CoprodI.of p.2).prod =
        ⁅CoprodI.of (M := factor H B) (i := false) z,
          CoprodI.of (M := factor H B) (i := true) b⁆ := by
      simp [letters]
      group
    _ = 1 := hcomm

/-- Exact truth table of the gate. -/
@[simp] theorem gate_eq_one_iff {z : H} (hz : z ≠ 1) (b : B) :
    gate z b = 1 ↔ b = 1 := by
  constructor
  · intro h
    by_contra hb
    exact gate_ne_one hz hb h
  · rintro rfl
    exact gate_one z

/-- The commutator gate is injective as a pointed map. -/
theorem gate_injective {z : H} (hz : z ≠ 1) :
    Function.Injective (gate (B := B) z) := by
  intro b c hbc
  have hcomm :
      gate z⁻¹ (c⁻¹ * b) = (1 : H ∗ B) := by
    rw [gate]
    apply commutatorElement_eq_one_iff_commute.mpr
    have h : Monoid.Coprod.inr b * (Monoid.Coprod.inl z)⁻¹ *
          (Monoid.Coprod.inr b)⁻¹ =
        Monoid.Coprod.inr c * (Monoid.Coprod.inl z)⁻¹ *
          (Monoid.Coprod.inr c)⁻¹ := by
      calc
        Monoid.Coprod.inr b * (Monoid.Coprod.inl z)⁻¹ *
            (Monoid.Coprod.inr b)⁻¹ =
            (Monoid.Coprod.inl z)⁻¹ * gate z b := by
              rw [gate]
              group
        _ = (Monoid.Coprod.inl z)⁻¹ * gate z c := by rw [hbc]
        _ = Monoid.Coprod.inr c * (Monoid.Coprod.inl z)⁻¹ *
            (Monoid.Coprod.inr c)⁻¹ := by
              rw [gate]
              group
    show (Monoid.Coprod.inl z)⁻¹ * Monoid.Coprod.inr (c⁻¹ * b) =
      Monoid.Coprod.inr (c⁻¹ * b) * (Monoid.Coprod.inl z)⁻¹
    simp only [map_mul, map_inv]
    calc
      (Monoid.Coprod.inl z)⁻¹ *
          ((Monoid.Coprod.inr c)⁻¹ * Monoid.Coprod.inr b) =
          (Monoid.Coprod.inr c)⁻¹ *
            (Monoid.Coprod.inr c * (Monoid.Coprod.inl z)⁻¹ *
              (Monoid.Coprod.inr c)⁻¹) * Monoid.Coprod.inr b := by group
      _ = (Monoid.Coprod.inr c)⁻¹ *
            (Monoid.Coprod.inr b * (Monoid.Coprod.inl z)⁻¹ *
              (Monoid.Coprod.inr b)⁻¹) * Monoid.Coprod.inr b := by rw [← h]
      _ = ((Monoid.Coprod.inr c)⁻¹ * Monoid.Coprod.inr b) *
            (Monoid.Coprod.inl z)⁻¹ := by group
  have hd : c⁻¹ * b = 1 :=
    (gate_eq_one_iff (B := B) (inv_ne_one.mpr hz) (c⁻¹ * b)).mp hcomm
  calc
    b = c * (c⁻¹ * b) := by group
    _ = c * 1 := by rw [hd]
    _ = c := mul_one c

/-- The gate is natural in the control group. -/
theorem gate_natural {C : Type u} [Group C] (z : H) (f : B →* C) (b : B) :
    Monoid.Coprod.lift Monoid.Coprod.inl (Monoid.Coprod.inr.comp f) (gate z b)
      = gate z (f b) := by
  simp [gate]

/-- The faithful pointed map is the standard nonabelian commutator cocycle. -/
theorem gate_mul (z : H) (b c : B) :
    gate z (b * c) = gate z b * Monoid.Coprod.inr b * gate z c *
      (Monoid.Coprod.inr b)⁻¹ := by
  simp only [gate, map_mul]
  group

end FaithfulRadicalCocycle
end GroupApproximation
