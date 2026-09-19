/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Bases

/-!
# Problem XXII of Schafhauser, Tikuisis and White: the trace problem has a negative answer

Schafhauser, Tikuisis and White, *99 problems in C⋆-algebras* (arXiv:2506.10902v2, §7, p. 24),
print Problem XXII for a C⋆-algebra `A` whose trace simplex `T(A)` is non-empty and compact:

> Are all traces on Ā^{T(A)} automatically ‖·‖_{2,T(A)}-continuous? Equivalently, is the canonical
> embedding T(A) ⊆ T(Ā^{T(A)}) an equality?

The problem cites Question 1.1 of Carrión, Castillejos, Evington, Gabe, Schafhauser, Tikuisis and
White, *Tracially complete C⋆-algebras* (arXiv:2310.20594v6), below CCEGSTW, whose notions it uses.

* **Tracially complete** (CCEGSTW Definition 3.4): a pair `(M, X)` of a C⋆-algebra `M` and a
  compact convex set `X ⊆ T(M)` that is a faithful set of traces, such that the unit ball of `M` is
  `‖·‖_{2,X}`-complete, where `‖a‖_{2,X} = sup_{τ ∈ X} τ(a⋆ a)^{1/2}`. CCEGSTW add that `X` is
  implicitly non-empty.
* **Factorial** (Definition 3.13): `X` is a closed face of `T(M)`.
* **Tracial completion** (Definition 3.19): for a compact convex `X ⊆ T(A)`, `Ā^X` is the
  C⋆-algebra of norm-bounded `‖·‖_{2,X}`-Cauchy sequences in `A` modulo the norm-bounded
  `‖·‖_{2,X}`-null ones, and `X~ ⊆ T(Ā^X)` is the set of traces induced by traces in `X`. The pair
  `(Ā^X, X~)` is tracially complete, and factorial exactly when `X` is a face (Proposition 3.23).

The Challenge does not construct `Ā^{T(A)}`; it characterises it. A unital ⋆-homomorphism
`α : A → M` *presents* a tracially complete pair `(M, X)` as the tracial completion of `A`
(`IsUniformTracialCompletion α X`) when every tracial state of `A` is `σ ∘ α` for exactly one
`σ ∈ X` and `α(A)` is `‖·‖_{2,X}`-dense in `M`. Then `(M, X) ≅ (Ā^{T(A)}, T(A)~)` compatibly with
`α`. This is CCEGSTW Corollary 3.29(i) applied to the C⋆-subalgebra `α(A)`: every tracial state of
`A` factors through `α`, so `ker α` is `‖·‖_{2,T(A)}`-null, bounded sequences in `α(A)` lift to
bounded sequences in `A` with the same two-norms, and restriction identifies `T(α(A))` with `X`
and with `T(A)`.

The statement block answers both forms of the printed question in the negative for such a
presentation, with `A` separable: some trace on `M` is not `‖·‖_{2,X}`-continuous, and `X ≠ T(M)`.
It also records that the `‖·‖_{2,X}`-continuous traces are exactly the members of `X` (CCEGSTW
Proposition 3.15). The pair is factorial, so the second theorem answers CCEGSTW Question 1.1, the
trace problem for factorial tracially complete C⋆-algebras, in the negative as well.

## Vocabulary

* `TracialState A` is a linear functional with `τ(1) = 1`, `τ(a⋆ a) ≥ 0` and `τ(ab) = τ(ba)`.
  Tracial states carry the weak⋆ topology `tracialStateTopology`, induced by the evaluations.
* `uniformTwoNorm X a` is `‖a‖_{2,X}`, the supremum over `τ ∈ X` of `τ(a⋆ a)^{1/2}`.
* `IsFaithfulTraceSet X` says that `‖·‖_{2,X}` is a norm, and `UnitBallUniformTwoComplete X` that
  the unit ball is `‖·‖_{2,X}`-complete, by sequences.
* `IsConvexTraceSet X` and `IsFaceTraceSet X` say that `X` is convex, or a face of `T(A)`. A convex
  combination of tracial states is stated pointwise, as a tracial state `ρ` with
  `ρ(a) = t σ(a) + (1 - t) τ(a)` for all `a`.
* `IsTraciallyComplete X` and `IsFactorialTraciallyComplete X` are Definitions 3.4 and 3.13.
* `IsUniformTwoContinuous X σ` says `σ(xₖ) → 0` whenever `‖xₖ‖_{2,X} → 0`; for a linear functional
  this is continuity for the seminorm `‖·‖_{2,X}`.
* `IsUniformTracialCompletion α X` is the presentation of `(Ā^{T(A)}, T(A)~)` described above.

Mathlib's `CStarAlgebra` is unital, and tracially complete C⋆-algebras are unital (CCEGSTW
Proposition 3.9). Algebras are quantified over `Type`.

The prose of this module was written by Claude (Anthropic).
-/

namespace STWProblemXXII

noncomputable section

-- BEGIN SHARED BLOCK (kept byte-identical in `Palomar/STWProblemXXIIChallenge.lean` and `Palomar/STWProblemXXIISolution.lean`)

open Filter
open scoped ComplexOrder

/-- A tracial state on a unital C⋆-algebra: a linear functional that is unital, nonnegative on
every `x⋆ x`, and invariant under swapping the factors of a product. -/
structure TracialState (A : Type*) [CStarAlgebra A] where
  toLinearMap : A →ₗ[ℂ] ℂ
  map_one : toLinearMap 1 = 1
  map_star_mul_self_nonneg : ∀ x : A, 0 ≤ toLinearMap (star x * x)
  map_mul_comm : ∀ x y : A, toLinearMap (x * y) = toLinearMap (y * x)

/-- The weak⋆ topology on tracial states: the coarsest topology making every evaluation
`τ ↦ τ(a)` continuous. -/
instance tracialStateTopology {A : Type*} [CStarAlgebra A] : TopologicalSpace (TracialState A) :=
  TopologicalSpace.induced (fun (τ : TracialState A) (a : A) ↦ τ.toLinearMap a) inferInstance

/-- The uniform two-norm `‖a‖_{2,X} = sup_{τ ∈ X} τ(a⋆ a)^{1/2}` (CCEGSTW Definition 3.1). -/
def uniformTwoNorm {A : Type*} [CStarAlgebra A] (X : Set (TracialState A)) (a : A) : ℝ :=
  sSup ((fun τ : TracialState A ↦ Real.sqrt (τ.toLinearMap (star a * a)).re) '' X)

/-- `X` is faithful: `a = 0` whenever `τ(a⋆ a) = 0` for every `τ ∈ X`, so `‖·‖_{2,X}` is a norm. -/
def IsFaithfulTraceSet {A : Type*} [CStarAlgebra A] (X : Set (TracialState A)) : Prop :=
  ∀ a : A, (∀ τ ∈ X, τ.toLinearMap (star a * a) = 0) → a = 0

/-- The unit ball is `‖·‖_{2,X}`-complete: every `‖·‖_{2,X}`-Cauchy sequence of norm at most `1`
has a `‖·‖_{2,X}`-limit of norm at most `1`. -/
def UnitBallUniformTwoComplete {A : Type*} [CStarAlgebra A] (X : Set (TracialState A)) : Prop :=
  ∀ x : ℕ → A, (∀ k, ‖x k‖ ≤ 1) →
    (∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, uniformTwoNorm X (x k - x l) < ε) →
      ∃ a : A, ‖a‖ ≤ 1 ∧ Tendsto (fun k ↦ uniformTwoNorm X (x k - a)) atTop (nhds 0)

/-- `X` is convex: a tracial state that is a convex combination of two members of `X` lies in
`X`. -/
def IsConvexTraceSet {A : Type*} [CStarAlgebra A] (X : Set (TracialState A)) : Prop :=
  ∀ σ ∈ X, ∀ τ ∈ X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ ρ : TracialState A,
    (∀ a : A, ρ.toLinearMap a =
      (t : ℂ) * σ.toLinearMap a + ((1 - t : ℝ) : ℂ) * τ.toLinearMap a) → ρ ∈ X

/-- `X` is a face of `T(A)`: it is convex, and whenever a proper convex combination of two tracial
states lies in `X`, both of them lie in `X`. -/
def IsFaceTraceSet {A : Type*} [CStarAlgebra A] (X : Set (TracialState A)) : Prop :=
  IsConvexTraceSet X ∧ ∀ σ τ : TracialState A, ∀ t : ℝ, 0 < t → t < 1 → ∀ ρ : TracialState A,
    (∀ a : A, ρ.toLinearMap a =
      (t : ℂ) * σ.toLinearMap a + ((1 - t : ℝ) : ℂ) * τ.toLinearMap a) →
      ρ ∈ X → σ ∈ X ∧ τ ∈ X

/-- **CCEGSTW Definition 3.4.** `(A, X)` is a tracially complete C⋆-algebra: `X` is a non-empty
compact convex set of tracial states, `‖·‖_{2,X}` is a norm, and the unit ball of `A` is
`‖·‖_{2,X}`-complete. -/
structure IsTraciallyComplete {A : Type*} [CStarAlgebra A] (X : Set (TracialState A)) : Prop where
  nonempty : X.Nonempty
  isCompact : IsCompact X
  isConvex : IsConvexTraceSet X
  faithful : IsFaithfulTraceSet X
  unitBallComplete : UnitBallUniformTwoComplete X

/-- **CCEGSTW Definition 3.13.** A tracially complete C⋆-algebra `(A, X)` is factorial: `X` is a
closed face of `T(A)`. -/
structure IsFactorialTraciallyComplete {A : Type*} [CStarAlgebra A]
    (X : Set (TracialState A)) : Prop where
  isTraciallyComplete : IsTraciallyComplete X
  isClosed : IsClosed X
  isFace : IsFaceTraceSet X

/-- A tracial state `σ` is `‖·‖_{2,X}`-continuous: `σ(xₖ) → 0` whenever `‖xₖ‖_{2,X} → 0`. -/
def IsUniformTwoContinuous {A : Type*} [CStarAlgebra A] (X : Set (TracialState A))
    (σ : TracialState A) : Prop :=
  ∀ x : ℕ → A, Tendsto (fun k ↦ uniformTwoNorm X (x k)) atTop (nhds 0) →
    Tendsto (fun k ↦ σ.toLinearMap (x k)) atTop (nhds 0)

/-- `α : A → M` presents `(M, X)` as the uniform tracial completion `(Ā^{T(A)}, T(A)~)` of `A`
(CCEGSTW Definition 3.19, Corollary 3.29(i)): `(M, X)` is tracially complete, every tracial state
of `A` is `σ ∘ α` for exactly one `σ ∈ X`, and `α(A)` is `‖·‖_{2,X}`-dense in `M`. -/
structure IsUniformTracialCompletion {A M : Type*} [CStarAlgebra A] [CStarAlgebra M]
    (α : A →⋆ₐ[ℂ] M) (X : Set (TracialState M)) : Prop where
  isTraciallyComplete : IsTraciallyComplete X
  existsUnique_restrict : ∀ τ : TracialState A,
    ∃! σ : TracialState M, σ ∈ X ∧ ∀ a : A, σ.toLinearMap (α a) = τ.toLinearMap a
  dense : ∀ m : M, ∃ x : ℕ → A,
    Tendsto (fun k ↦ uniformTwoNorm X (m - α (x k))) atTop (nhds 0)

-- END SHARED BLOCK

/-- **Problem XXII has a negative answer.** There are a separable unital C⋆-algebra `A`, with
`T(A)` non-empty and compact, and a presentation `α : A → M` of its uniform tracial completion
`(M, X) = (Ā^{T(A)}, T(A)~)`, such that the `‖·‖_{2,X}`-continuous traces on `M` are exactly the
members of `X`, some trace on `M` is not `‖·‖_{2,X}`-continuous, and `X ≠ T(M)`. -/
theorem exists_uniformTracialCompletion_with_discontinuous_trace :
    ∃ (A : Type) (_ : CStarAlgebra A) (M : Type) (_ : CStarAlgebra M) (α : A →⋆ₐ[ℂ] M)
      (X : Set (TracialState M)),
      TopologicalSpace.SeparableSpace A ∧
      (Set.univ : Set (TracialState A)).Nonempty ∧ IsCompact (Set.univ : Set (TracialState A)) ∧
      IsUniformTracialCompletion α X ∧
      (∀ σ : TracialState M, σ ∈ X ↔ IsUniformTwoContinuous X σ) ∧
      (∃ σ : TracialState M, ¬ IsUniformTwoContinuous X σ) ∧ X ≠ Set.univ := by
  sorry

/-- **The trace problem fails for factorial tracially complete C⋆-algebras.** Some factorial
tracially complete C⋆-algebra `(M, X)` has a trace that is not `‖·‖_{2,X}`-continuous, and
`X ≠ T(M)`; its `‖·‖_{2,X}`-continuous traces are exactly the members of `X`. -/
theorem exists_factorial_traciallyComplete_with_discontinuous_trace :
    ∃ (M : Type) (_ : CStarAlgebra M) (X : Set (TracialState M)),
      IsFactorialTraciallyComplete X ∧
      (∀ σ : TracialState M, σ ∈ X ↔ IsUniformTwoContinuous X σ) ∧
      (∃ σ : TracialState M, ¬ IsUniformTwoContinuous X σ) ∧ X ≠ Set.univ := by
  sorry

end

end STWProblemXXII
