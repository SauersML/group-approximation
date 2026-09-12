import GroupApproximation.Analysis.CoronaTraceCompactness
import GroupApproximation.Analysis.CStarStatePullback

/-!
# Coordinate-state finite solvability for a C-star corona

`CoronaTraceCompactness` turns finite state constraints on the bounded product
into a tracial state on its `c₀` corona.  This file supplies the coordinate
bridge needed to apply that theorem.

The only input is an *arbitrarily late* coordinate-state solvability
statement: for each finite family of bounded sequences and each lower bound on
the coordinate, one coordinate state detects `h` and annihilates the displayed
self-commutators.  Pulling the state back along coordinate evaluation gives a
state on the bounded product.  Because the coordinate can be chosen
arbitrarily late, every finite family from the `c₀` ideal is automatically as
small as the compactness argument requests.

No Jordan decomposition or Cuntz--Pedersen separation theorem is used.
-/

namespace GroupApproximation
namespace CoronaCoordinateStateCompactness

open Filter PolarLiftingGeneralCStar
open CStarState CuntzPedersenCoronaObstruction FiniteTraceCompactness
open CoronaTraceCompactness

noncomputable section

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)]

/-- Evaluation of a bounded dependent sequence at one coordinate, as a
unital star-algebra homomorphism. -/
def coordinateStarAlgHom (n : ℕ) :
    BoundedCStarSequence D →⋆ₐ[ℂ] D n where
  toFun x := x n
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp] theorem coordinateStarAlgHom_apply (n : ℕ)
    (x : BoundedCStarSequence D) :
    coordinateStarAlgHom (D := D) n x = x n := rfl

/-- A state on one coordinate, pulled back to the bounded product. -/
def coordinateState (n : ℕ) (ψ : State (D n)) :
    State (BoundedCStarSequence D) :=
  ψ.comp (coordinateStarAlgHom (D := D) n)

@[simp] theorem coordinateState_apply (n : ℕ) (ψ : State (D n))
    (x : BoundedCStarSequence D) :
    (coordinateState (D := D) n ψ).toCLM x = ψ.toCLM (x n) := rfl

/-- Finite commutator constraints can be solved by coordinate states at
arbitrarily late coordinates, while the chosen sequence is detected there.

The lower-bound parameter is essential: it is what makes all finitely many
`c₀` constraints small at the same selected coordinate. -/
def ArbitrarilyLateCoordinateStateConstraints
    (h : BoundedCStarSequence D) : Prop :=
  ∀ (S : Finset (BoundedCStarSequence D)) (floor : ℕ),
    ∃ n : ℕ, floor ≤ n ∧ ∃ ψ : State (D n),
      ψ.toCLM (h n) = 1 ∧
      ∀ z ∈ S, ψ.toCLM (selfCommutator (z n)) = 0

private theorem state_norm_apply_le {A : Type*} [CStarAlgebra A]
    [Nontrivial A] (ψ : State A) (x : A) :
    ‖ψ.toCLM x‖ ≤ ‖x‖ := by
  calc
    ‖ψ.toCLM x‖ ≤ ‖ψ.toCLM‖ * ‖x‖ := ψ.toCLM.le_opNorm x
    _ ≤ 1 * ‖x‖ :=
      mul_le_mul_of_nonneg_right ψ.norm_le (norm_nonneg x)
    _ = ‖x‖ := one_mul _

private theorem selfCommutator_apply (z : BoundedCStarSequence D) (n : ℕ) :
    selfCommutator z n = selfCommutator (z n) := rfl

/-- The abstract coordinate hypothesis supplies exactly the finite product
state required by `FiniteTraceCompactness`.  Smallness on finitely many null
sequences is derived here from their convergence to zero, rather than included
as an additional assumption. -/
theorem exists_product_state_for_vanishing_constraints
    (h : BoundedCStarSequence D)
    (hcoord : ArbitrarilyLateCoordinateStateConstraints h)
    (K : VanishingConstraintIndex
      (nullCStarSequenceIdeal D atTop : Set (BoundedCStarSequence D))) :
    ∃ φ : State (BoundedCStarSequence D),
      φ.toCLM h = 1 ∧
      (∀ z ∈ K.commutators,
        φ.toCLM (selfCommutator z) = 0) ∧
      ∀ a ∈ K.vanishing,
        ‖φ.toCLM a.1‖ ≤ 1 / (K.precision + 1 : ℝ) := by
  have hepsilon : 0 < 1 / (K.precision + 1 : ℝ) := by positivity
  have htail : ∀ᶠ n in atTop, ∀ a ∈ K.vanishing,
      ‖a.1 n‖ ≤ 1 / (K.precision + 1 : ℝ) :=
    (Filter.eventually_all_finset K.vanishing).mpr fun a _ ↦ by
      exact a.property.eventually_le_const hepsilon
  obtain ⟨floor, hfloor⟩ := Filter.eventually_atTop.1 htail
  obtain ⟨n, hn, ψ, hψh, hψcomm⟩ := hcoord K.commutators floor
  let φ : State (BoundedCStarSequence D) := coordinateState n ψ
  refine ⟨φ, ?_, ?_, ?_⟩
  · exact hψh
  · intro z hz
    simpa only [φ, coordinateState_apply, selfCommutator_apply] using
      hψcomm z hz
  · intro a ha
    calc
      ‖φ.toCLM a.1‖ = ‖ψ.toCLM (a.1 n)‖ := rfl
      _ ≤ ‖a.1 n‖ := state_norm_apply_le ψ (a.1 n)
      _ ≤ 1 / (K.precision + 1 : ℝ) := hfloor n hn a ha

/-- Arbitrarily late coordinate-state solvability yields a tracial state on
the `c₀` corona which detects the class of `h`.  This is the complete compactness
and quotient step: the remaining application-specific task is solely to prove
`ArbitrarilyLateCoordinateStateConstraints h` for the proposed blocks. -/
theorem exists_corona_tracialState_of_arbitrarilyLate_coordinate_states
    (h : BoundedCStarSequence D)
    (hcoord : ArbitrarilyLateCoordinateStateConstraints h) :
    ∃ σ : TracialState (CStarProductCorona D atTop),
      σ (cStarProductCoronaQuotient D atTop h) = 1 := by
  apply exists_corona_tracialState_of_finite_state_constraints h
  exact exists_product_state_for_vanishing_constraints h hcoord

end

end CoronaCoordinateStateCompactness
end GroupApproximation

