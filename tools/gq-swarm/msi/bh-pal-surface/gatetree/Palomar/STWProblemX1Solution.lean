/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Bases
import GroupApproximation.PalomarBridges.X1

/-!
# Proof of Problem X(1) of Schafhauser, Tikuisis and White

This file repeats the challenge's shared block byte for byte, translates the development's
vocabulary into it, and proves the two theorems `Palomar/comparator-stw-x1.json` selects.

* `GroupApproximation.NinetyNineProblems.amenableNonQuasidiagonalTrace` is the witness: the
  maximal group C⋆-algebra `MaximalGroupCStar MarkedGroup` with its canonical tracial state,
  which is amenable and not quasidiagonal. It lives in `Type 1`.
* `GroupApproximation.PalomarBridges.X1.amenableNonQuasidiagonalTrace_zero` moves the witness to
  `Type` through `Shrink`, using separability.
* The challenge's definitions are the development's, field for field. `FiniteCarrier` is
  `FiniteModel`, `normalizedTrace` is `normTrace` and `hilbertSchmidtNorm` is `hsNorm`.
  `IsCompletelyPositive` is `IsCompletelyPositiveOnMatrices` with its clauses `im = 0` and
  `0 ≤ re` combined into `0 ≤` for the order on `ℂ`.
* The universal statement follows from the existential without excluded middle.

The prose of this module was written by Claude (Anthropic).
-/

namespace STWProblemX1

noncomputable section

-- BEGIN SHARED BLOCK (kept byte-identical in `Palomar/STWProblemX1Challenge.lean` and `Palomar/STWProblemX1Solution.lean`)

open Filter
open scoped ComplexOrder Matrix.Norms.L2Operator

/-- A finite type with decidable equality, used as the index set of a matrix algebra `M_Y(ℂ)`. -/
structure FiniteCarrier where
  carrier : Type
  fintype : Fintype carrier
  decidableEq : DecidableEq carrier

instance finiteCarrierCoeSort : CoeSort FiniteCarrier Type :=
  ⟨FiniteCarrier.carrier⟩

@[reducible, instance] def finiteCarrierFintype (Y : FiniteCarrier) : Fintype Y :=
  Y.fintype

@[reducible, instance] def finiteCarrierDecidableEq (Y : FiniteCarrier) : DecidableEq Y :=
  Y.decidableEq

/-- The normalized trace `tr(T) = trace T / |Y|` on `M_Y(ℂ)`. -/
def normalizedTrace (Y : FiniteCarrier) (T : Matrix Y Y ℂ) : ℂ :=
  Matrix.trace T / Fintype.card Y

/-- The normalized Hilbert–Schmidt norm `‖T‖₂ = (∑ᵢⱼ |Tᵢⱼ|² / |Y|)^{1/2}` on `M_Y(ℂ)`. -/
def hilbertSchmidtNorm (Y : FiniteCarrier) (T : Matrix Y Y ℂ) : ℝ :=
  Real.sqrt ((∑ i : Y, ∑ j : Y, Complex.normSq (T i j)) / Fintype.card Y)

/-- A linear map `φ : A → M_Y(ℂ)` is completely positive: for all `a₁, …, aₘ ∈ A` and all
`ξ₁, …, ξₘ ∈ ℂ^Y`, the form `∑ᵢⱼ ⟨ξᵢ, φ(aᵢ⋆ aⱼ) ξⱼ⟩` is nonnegative. -/
def IsCompletelyPositive {A : Type*} [CStarAlgebra A] (Y : FiniteCarrier)
    (φ : A →ₗ[ℂ] Matrix Y Y ℂ) : Prop :=
  ∀ (m : ℕ) (a : Fin m → A) (ξ : Fin m → Y → ℂ),
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y,
      star (ξ i x) * φ (star (a i) * a j) x y * ξ j y

/-- A tracial state on a unital C⋆-algebra: a linear functional that is unital, nonnegative on
every `x⋆ x`, and invariant under swapping the factors of a product. -/
structure TracialState (A : Type*) [CStarAlgebra A] where
  toLinearMap : A →ₗ[ℂ] ℂ
  map_one : toLinearMap 1 = 1
  map_star_mul_self_nonneg : ∀ x : A, 0 ≤ toLinearMap (star x * x)
  map_mul_comm : ∀ x y : A, toLinearMap (x * y) = toLinearMap (y * x)

/-- Models for an amenable trace (Brown, Theorem 3.1.6(2)): unital completely positive maps into
matrix algebras, asymptotically multiplicative in the normalized Hilbert–Schmidt norm, whose
normalized traces converge to `τ`. -/
structure AmenableTraceModel {A : Type*} [CStarAlgebra A] (τ : TracialState A) where
  space : ℕ → FiniteCarrier
  map : ∀ n : ℕ, A →ₗ[ℂ] Matrix (space n) (space n) ℂ
  map_one : ∀ n : ℕ, map n 1 = 1
  completelyPositive : ∀ n : ℕ, IsCompletelyPositive (space n) (map n)
  tendsto_mul : ∀ a b : A,
    Tendsto (fun n ↦ hilbertSchmidtNorm (space n) (map n (a * b) - map n a * map n b))
      atTop (nhds 0)
  tendsto_trace : ∀ a : A,
    Tendsto (fun n ↦ ‖τ.toLinearMap a - normalizedTrace (space n) (map n a)‖) atTop (nhds 0)

/-- Models for a quasidiagonal trace (Brown, Definition 3.3.1): unital completely positive maps
into matrix algebras, asymptotically multiplicative in operator norm, whose normalized traces
converge to `τ`. -/
structure QuasidiagonalTraceModel {A : Type*} [CStarAlgebra A] (τ : TracialState A) where
  space : ℕ → FiniteCarrier
  map : ∀ n : ℕ, A →ₗ[ℂ] Matrix (space n) (space n) ℂ
  map_one : ∀ n : ℕ, map n 1 = 1
  completelyPositive : ∀ n : ℕ, IsCompletelyPositive (space n) (map n)
  tendsto_mul : ∀ a b : A,
    Tendsto (fun n ↦ ‖map n (a * b) - map n a * map n b‖) atTop (nhds 0)
  tendsto_trace : ∀ a : A,
    Tendsto (fun n ↦ ‖τ.toLinearMap a - normalizedTrace (space n) (map n a)‖) atTop (nhds 0)

/-- `τ` is an amenable trace. -/
def IsAmenableTrace {A : Type*} [CStarAlgebra A] (τ : TracialState A) : Prop :=
  Nonempty (AmenableTraceModel τ)

/-- `τ` is a quasidiagonal trace. -/
def IsQuasidiagonalTrace {A : Type*} [CStarAlgebra A] (τ : TracialState A) : Prop :=
  Nonempty (QuasidiagonalTraceModel τ)

-- END SHARED BLOCK

section Bridge

/-- A finite model of the development, as a challenge carrier. -/
def carrierOf (Y : GroupApproximation.FiniteModel) : FiniteCarrier :=
  ⟨Y.carrier, Y.fintype, Y.decidableEq⟩

/-- A challenge carrier, as a finite model of the development. -/
def modelOf (Y : FiniteCarrier) : GroupApproximation.FiniteModel :=
  ⟨Y.carrier, Y.fintype, Y.decidableEq⟩

variable {A : Type} [CStarAlgebra A]

/-- A tracial state of the development, as a challenge tracial state. -/
def tracialStateOf (τ : GroupApproximation.TracialState A) : TracialState A where
  toLinearMap := τ.toLinearMap
  map_one := τ.map_one
  map_star_mul_self_nonneg := τ.map_star_mul_self_nonneg
  map_mul_comm := τ.map_mul_comm

theorem isCompletelyPositive_of {Y : GroupApproximation.FiniteModel}
    {φ : A →ₗ[ℂ] Matrix Y Y ℂ}
    (h : GroupApproximation.Quasidiagonal.IsCompletelyPositiveOnMatrices Y ⇑φ) :
    IsCompletelyPositive (carrierOf Y) φ := by
  intro m a ξ
  obtain ⟨him, hre⟩ := h m a ξ
  simp only [starRingEnd_apply] at him hre
  exact Complex.nonneg_iff.2 ⟨hre, him.symm⟩

theorem isCompletelyPositiveOnMatrices_of {Y : FiniteCarrier} {φ : A →ₗ[ℂ] Matrix Y Y ℂ}
    (h : IsCompletelyPositive Y φ) :
    GroupApproximation.Quasidiagonal.IsCompletelyPositiveOnMatrices (modelOf Y) ⇑φ := by
  intro m a w
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.1 (h m a w)
  simp only [starRingEnd_apply]
  exact ⟨him.symm, hre⟩

/-- An amenable trace model of the development is a challenge amenable trace model. -/
def amenableTraceModelOf {τ : GroupApproximation.TracialState A}
    (M : GroupApproximation.Quasidiagonal.AmenableTraceModel (fun a : A ↦ τ a)) :
    AmenableTraceModel (tracialStateOf τ) where
  space n := carrierOf (M.space n)
  map := M.map
  map_one := M.map_one
  completelyPositive n := isCompletelyPositive_of (M.completelyPositive n)
  tendsto_mul := M.tendsto_mul_hs
  tendsto_trace := M.tendsto_trace

/-- A challenge quasidiagonal trace model is a quasidiagonal trace model of the development. -/
def quasidiagonalTraceModelOf {τ : GroupApproximation.TracialState A}
    (N : QuasidiagonalTraceModel (tracialStateOf τ)) :
    GroupApproximation.Quasidiagonal.QuasidiagonalTraceModel (fun a : A ↦ τ a) where
  space n := modelOf (N.space n)
  map := N.map
  map_one := N.map_one
  completelyPositive n := isCompletelyPositiveOnMatrices_of (N.completelyPositive n)
  tendsto_mul := N.tendsto_mul
  tendsto_trace := N.tendsto_trace

end Bridge

/-- The development's existence statement, at universe zero, gives the challenge's. -/
theorem exists_separable_amenable_not_quasidiagonal_of
    (h : GroupApproximation.NinetyNineProblems.AmenableNonQuasidiagonalTrace.{0}) :
    ∃ (A : Type) (_ : CStarAlgebra A), TopologicalSpace.SeparableSpace A ∧
      ∃ τ : TracialState A, IsAmenableTrace τ ∧ ¬ IsQuasidiagonalTrace τ := by
  obtain ⟨A, _inst, τ, hsep, ⟨M⟩, hnot⟩ := h
  refine ⟨A, _inst, hsep, tracialStateOf τ, ⟨amenableTraceModelOf M⟩, ?_⟩
  rintro ⟨N⟩
  exact hnot ⟨quasidiagonalTraceModelOf N⟩

/-- **Problem X(1) has a negative answer.** Some separable unital C⋆-algebra carries a tracial
state that is amenable and not quasidiagonal. -/
theorem exists_separable_amenable_not_quasidiagonal :
    ∃ (A : Type) (_ : CStarAlgebra A), TopologicalSpace.SeparableSpace A ∧
      ∃ τ : TracialState A, IsAmenableTrace τ ∧ ¬ IsQuasidiagonalTrace τ := by
  exact exists_separable_amenable_not_quasidiagonal_of
    GroupApproximation.PalomarBridges.X1.amenableNonQuasidiagonalTrace_zero

/-- **The printed universal fails**: not every amenable tracial state on a separable unital
C⋆-algebra is quasidiagonal. -/
theorem not_every_amenable_trace_quasidiagonal :
    ¬ ∀ (A : Type) [CStarAlgebra A] [TopologicalSpace.SeparableSpace A] (τ : TracialState A),
      IsAmenableTrace τ → IsQuasidiagonalTrace τ := by
  intro h
  obtain ⟨A, _inst, _hsep, τ, hamen, hnot⟩ := exists_separable_amenable_not_quasidiagonal
  exact hnot (h A τ hamen)

end

end STWProblemX1
