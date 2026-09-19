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

/-!
# Problem X(1) of Schafhauser, Tikuisis and White: amenable traces need not be quasidiagonal

Schafhauser, Tikuisis and White, *99 problems in C⋆-algebras* (arXiv:2506.10902v2, p. 15), print

> Problem X. (1) Are amenable traces on C∗-algebras necessarily quasidiagonal?

The question is N. P. Brown's, from *Invariant means and finite representation theory of
C⋆-algebras*, Mem. Amer. Math. Soc. **184** (2006), no. 865. For a tracial state `τ` on a unital
separable C⋆-algebra `A`, Brown calls `τ`

* **amenable** when (Theorem 3.1.6(2), the equivalent form used as the definition here) there are
  unital completely positive maps `φₙ : A → M_{k(n)}(ℂ)` with `‖φₙ(ab) − φₙ(a)φₙ(b)‖₂ → 0` and
  `tr(φₙ(a)) → τ(a)` for all `a, b ∈ A`, where `‖·‖₂` is the normalized Hilbert–Schmidt norm and
  `tr` the normalized trace;
* **quasidiagonal** (Definition 3.3.1) when there are such maps with
  `‖φₙ(ab) − φₙ(a)φₙ(b)‖ → 0` in operator norm.

The two definitions differ in one norm. The statement block answers the question in the negative,
as an explicit existence statement and as the failure of the printed universal.

## Vocabulary

* `FiniteCarrier` is a finite type with decidable equality, the index set of a matrix algebra.
* `normalizedTrace Y T` is `trace T / |Y|`, and `hilbertSchmidtNorm Y T` is
  `(∑ᵢⱼ |Tᵢⱼ|² / |Y|)^{1/2}`. Matrix algebras carry the operator norm of `ℓ²(Y)`
  (`Matrix.Norms.L2Operator`), which is their C⋆-norm.
* `IsCompletelyPositive Y φ` asks every quadratic form `∑ᵢⱼ ⟨ξᵢ, φ(aᵢ⋆ aⱼ) ξⱼ⟩` to be
  nonnegative, that is, every block matrix `[φ(aᵢ⋆ aⱼ)]` to be positive semidefinite. Positive
  elements of `M_m(A)` are sums of matrices `[aᵢ⋆ aⱼ]`, so this is complete positivity.
* `TracialState A` is a linear functional with `τ(1) = 1`, `τ(a⋆ a) ≥ 0` and `τ(ab) = τ(ba)`.
* `AmenableTraceModel τ` and `QuasidiagonalTraceModel τ` are the sequences of maps above, and
  `IsAmenableTrace τ` and `IsQuasidiagonalTrace τ` say that one exists.

Mathlib's `CStarAlgebra` is unital. Separability is a hypothesis of the universal statement, as in
Brown, and part of the conclusion of the existence statement; for separable algebras sequences of
maps suffice. The matrix sizes are not required to be positive: `τ(1) = 1` and the trace clause at
`a = 1` already make all but finitely many carriers nonempty. Algebras are quantified over `Type`.

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

/-- **Problem X(1) has a negative answer.** Some separable unital C⋆-algebra carries a tracial
state that is amenable and not quasidiagonal. -/
theorem exists_separable_amenable_not_quasidiagonal :
    ∃ (A : Type) (_ : CStarAlgebra A), TopologicalSpace.SeparableSpace A ∧
      ∃ τ : TracialState A, IsAmenableTrace τ ∧ ¬ IsQuasidiagonalTrace τ := by
  sorry

/-- **The printed universal fails**: not every amenable tracial state on a separable unital
C⋆-algebra is quasidiagonal. -/
theorem not_every_amenable_trace_quasidiagonal :
    ¬ ∀ (A : Type) [CStarAlgebra A] [TopologicalSpace.SeparableSpace A] (τ : TracialState A),
      IsAmenableTrace τ → IsQuasidiagonalTrace τ := by
  sorry

end

end STWProblemX1
