import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.CloseCPAP
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-27, part 1: Kraus-column maps `M_Y → A`

A column `G : Y → A` gives the linear map
`ψ_G(N) = ∑_{y, y'} N_{y y'} • (G y)⋆ (G y')`, which is `G⋆ (N ⊗ 1) G` in matrix notation.
This file proves the algebraic identities for these maps:

* `ψ_G 1 = ⟨G, G⟩`, where `⟨u, v⟩ = ∑_y (u y)⋆ (v y)` is the `A`-valued pairing;
* rank-one positivity: `ψ_G(v v⋆) = c⋆ c` with `c = ∑_y (v y)⋆ • G y`;
* `ψ_G(N⋆) = ψ_G(N)⋆`;
* the Hilbert-module identity `⟨N₁⋆ G, N₂ G⟩ = ψ_G(N₁ N₂)`;
* the shift identities used in Choi's inequality.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- The `A`-valued pairing `⟨u, v⟩ = ∑_y (u y)⋆ (v y)` on columns `Y → A`. -/
def choiEffrosPair {Y : Type} [Fintype Y] (u v : Y → A) : A :=
  ∑ y, star (u y) * v y

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosPair

/-- A scalar matrix acting on a column: `(N G) y = ∑_{y'} N_{y y'} • G y'`. -/
def choiEffrosAct {Y : Type} [Fintype Y] (N : Matrix Y Y ℂ) (G : Y → A) (y : Y) : A :=
  ∑ y', N y y' • G y'

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosAct

/-- The shifted column `y ↦ u y - G y * c`. -/
def choiEffrosShift {Y : Type} (u G : Y → A) (c : A) (y : Y) : A :=
  u y - G y * c

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosShift

/-- **The Kraus-column map** `ψ_G(N) = ⟨G, N G⟩ = ∑_{y,y'} N_{y y'} • (G y)⋆ (G y')`. -/
def choiEffrosKrausMap {Y : Type} [Fintype Y] (G : Y → A) : Matrix Y Y ℂ →ₗ[ℂ] A where
  toFun N := choiEffrosPair G (choiEffrosAct N G)
  map_add' N₁ N₂ := by
    show ∑ y, star (G y) * ∑ y', (N₁ + N₂) y y' • G y' =
      ∑ y, star (G y) * ∑ y', N₁ y y' • G y' + ∑ y, star (G y) * ∑ y', N₂ y y' • G y'
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [← mul_add, ← Finset.sum_add_distrib]
    refine congrArg (star (G y) * ·) (Finset.sum_congr rfl fun y' _ ↦ ?_)
    rw [Matrix.add_apply, add_smul]
  map_smul' z N := by
    show ∑ y, star (G y) * ∑ y', (z • N) y y' • G y' =
      z • ∑ y, star (G y) * ∑ y', N y y' • G y'
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [← mul_smul_comm, Finset.smul_sum]
    refine congrArg (star (G y) * ·) (Finset.sum_congr rfl fun y' _ ↦ ?_)
    rw [Matrix.smul_apply, smul_eq_mul, mul_smul]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosKrausMap

/-- The identity matrix acts trivially on columns. -/
theorem choiEffros_act_one {Y : Type} [Fintype Y] [DecidableEq Y] (G : Y → A) :
    choiEffrosAct (1 : Matrix Y Y ℂ) G = G := by
  funext y
  show ∑ y', (1 : Matrix Y Y ℂ) y y' • G y' = G y
  rw [Finset.sum_eq_single y]
  · rw [Matrix.one_apply_eq, one_smul]
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), zero_smul]
  · intro hy
    exact absurd (Finset.mem_univ y) hy

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffros_act_one

/-- The pairing is Hermitian: `⟨u, v⟩⋆ = ⟨v, u⟩`. -/
theorem choiEffros_star_pair {Y : Type} [Fintype Y] (u v : Y → A) :
    star (choiEffrosPair u v) = choiEffrosPair v u := by
  simp only [choiEffrosPair, star_sum, star_mul, star_star]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffros_star_pair

/-- **The Hilbert-module identity** `⟨N₁⋆ G, N₂ G⟩ = ψ_G(N₁ N₂)`. -/
theorem choiEffros_pair_act_act {Y : Type} [Fintype Y] (G : Y → A) (N₁ N₂ : Matrix Y Y ℂ) :
    choiEffrosPair (choiEffrosAct (star N₁) G) (choiEffrosAct N₂ G) =
      choiEffrosKrausMap G (N₁ * N₂) := by
  have hL : choiEffrosPair (choiEffrosAct (star N₁) G) (choiEffrosAct N₂ G) =
      ∑ y, ∑ y', ∑ y'', (N₁ y' y * N₂ y y'') • (star (G y') * G y'') := by
    show ∑ y, star (choiEffrosAct (star N₁) G y) * choiEffrosAct N₂ G y = _
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    show star (∑ y', (star N₁) y y' • G y') * ∑ y'', N₂ y y'' • G y'' = _
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y' _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y'' _ ↦ ?_
    rw [star_smul, Matrix.star_apply, star_star, smul_mul_smul_comm]
  have hR : choiEffrosKrausMap G (N₁ * N₂) =
      ∑ y', ∑ y'', ∑ y, (N₁ y' y * N₂ y y'') • (star (G y') * G y'') := by
    show ∑ y', star (G y') * ∑ y'', (N₁ * N₂) y' y'' • G y'' = _
    refine Finset.sum_congr rfl fun y' _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y'' _ ↦ ?_
    rw [Matrix.mul_apply, Finset.sum_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [mul_smul_comm]
  rw [hL, hR]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun y' _ ↦ Finset.sum_comm)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffros_pair_act_act

/-- **Unit.** `ψ_G 1 = ⟨G, G⟩`. -/
theorem choiEffros_krausMap_one {Y : Type} [Fintype Y] [DecidableEq Y] (G : Y → A) :
    choiEffrosKrausMap G (1 : Matrix Y Y ℂ) = choiEffrosPair G G := by
  show choiEffrosPair G (choiEffrosAct (1 : Matrix Y Y ℂ) G) = choiEffrosPair G G
  rw [choiEffros_act_one]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffros_krausMap_one
