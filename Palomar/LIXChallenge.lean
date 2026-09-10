/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.PathConnected

/-!
# STW Problem LIX: a simple unital C⋆-algebra that is not `K₁`-injective

Schafhauser, Tikuisis and White, *Nuclear C⋆-algebras: 99 problems*
(arXiv:2506.10902), print as Problem LIX, verbatim:

> Are all unital simple C*-algebras K₁-injective?

The three theorems below answer **no**, in increasing strength:

* `not_all_simple_unital_k1Injective` negates the printed question as stated;
* `exists_separable_simple_not_k1Injective` exhibits the counterexample as a
  **separable** simple unital C⋆-algebra;
* `exists_separable_simple_stage_two_witness` gives the sharpest form: a
  separable simple unital C⋆-algebra `A` with a unitary `u` that is not
  connected to `1` inside `U(A)`, while `diag (u, 1)` is already connected to
  `1` inside `U(M₂(A))`.  So the class of `u` dies at the very first
  stabilisation step, which is more than non-injectivity of
  `U(A)/U₀(A) → K₁(A)` asks.

## Vocabulary

Every notion is Mathlib's.  `CStarAlgebra A` is a *unital* C⋆-algebra
(`CStarAlgebra` extends `NormedRing`), so "unital" carries no separate
hypothesis.  `IsSimpleRing A` is Mathlib's simplicity: the only two-sided
ideals are `⊥` and `⊤`.  For a unital C⋆-algebra this agrees with C⋆-simplicity
(only the *closed* two-sided ideals are asked about), because a proper
two-sided ideal of a unital Banach algebra misses a neighbourhood of `1` and so
has proper closure.  `TopologicalSpace.SeparableSpace A` is separability.
`unitary A` is the unitary group, `Subgroup.pathComponentOne (unitary A)` is
`U₀(A)`, the path component of `1` in it, and `CStarMatrix (Fin n) (Fin n) A`
is `Mₙ(A)` with Mathlib's C⋆-norm.  The only definitions made here are the
corner matrix `diag (a, 1, …, 1)` and `K₁`-injectivity itself, documented
below.  All algebras are quantified over `Type`; the counterexample is a
concrete separable algebra built from matrices over `C(X, ℂ)`, so it lives
there, and `Type 0` is what the printed problem means.
-/

namespace ProblemLIX

noncomputable section

-- BEGIN SHARED BLOCK (kept byte-identical with `Palomar/LIXSolution.lean`)

/-- `diag (a, 1, …, 1)`: the `n × n` matrix over `A` whose top-left entry is
`a`, whose remaining diagonal entries are `1`, and whose off-diagonal entries
are `0`.  For `n = 2` this is `diag (a, 1)`, the standard stabilisation of `a`. -/
def cornerDiag (A : Type) [CStarAlgebra A] (n : ℕ) (a : A) :
    CStarMatrix (Fin n) (Fin n) A :=
  fun i j => if i = j then (if (i : ℕ) = 0 then a else 1) else 0

/-- `K₁`-injectivity of a unital C⋆-algebra `A`: the canonical homomorphism
`U(A)/U₀(A) → K₁(A)` is injective, where `U₀(A)` is the path component of `1`
in the unitary group.

`K₁(A)` is the direct limit of the groups `U(Mₙ(A))/U₀(Mₙ(A))` along the
stabilisation maps `u ↦ diag (u, 1)`, so the class of a unitary `u ∈ U(A)`
vanishes in `K₁(A)` exactly when `diag (u, 1, …, 1) ∈ U₀(Mₙ(A))` for some `n`,
and a group homomorphism is injective exactly when its kernel is trivial.  The
definition records precisely that: every unitary of `A` whose stabilisation is
connected to `1` in some matrix algebra over `A` is already connected to `1`
in `U(A)`.  The stabilised unitary is described by its underlying matrix, so
that no unitarity proof has to be packaged inside the statement.

Mathlib's C⋆-structure on `Mₙ(A)`, `CStarMatrix.instCStarAlgebra`, asks for a
partial order on `A` making it a `StarOrderedRing`.  A unital C⋆-algebra has
exactly one such order, the spectral order (`x ≤ y` iff `y - x` is positive),
and that is the one supplied. -/
def IsK1Injective (A : Type) [CStarAlgebra A] : Prop :=
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  ∀ u : unitary A,
    (∃ n : ℕ,
      ∃ w ∈ Subgroup.pathComponentOne (unitary (CStarMatrix (Fin (n + 1)) (Fin (n + 1)) A)),
        (w : CStarMatrix (Fin (n + 1)) (Fin (n + 1)) A) = cornerDiag A (n + 1) (u : A)) →
    u ∈ Subgroup.pathComponentOne (unitary A)

-- END SHARED BLOCK

/-- **STW Problem LIX has a negative answer**: it is not the case that every
nontrivial simple unital C⋆-algebra is `K₁`-injective. -/
theorem not_all_simple_unital_k1Injective :
    ¬ ∀ (A : Type) [CStarAlgebra A], Nontrivial A → IsSimpleRing A → IsK1Injective A := by
  sorry

/-- **The counterexample is separable**: there is a separable simple unital
C⋆-algebra that is not `K₁`-injective. -/
theorem exists_separable_simple_not_k1Injective :
    ∃ (A : Type) (_ : CStarAlgebra A),
      TopologicalSpace.SeparableSpace A ∧ IsSimpleRing A ∧ ¬ IsK1Injective A := by
  sorry

/-- **The sharp form**: a separable simple unital C⋆-algebra `A` carrying a
unitary `u` that is not connected to `1` in `U(A)`, although `diag (u, 1)` is
connected to `1` in `U(M₂(A))`.  The class of `u` therefore vanishes already at
the first stabilisation step, which refutes `K₁`-injectivity of `A` with `n = 1`
in `IsK1Injective`. -/
theorem exists_separable_simple_stage_two_witness :
    ∃ (A : Type) (_ : CStarAlgebra A),
      TopologicalSpace.SeparableSpace A ∧ IsSimpleRing A ∧
      (letI : PartialOrder A := CStarAlgebra.spectralOrder A
       letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
       ∃ u : unitary A, u ∉ Subgroup.pathComponentOne (unitary A) ∧
         ∃ w ∈ Subgroup.pathComponentOne (unitary (CStarMatrix (Fin 2) (Fin 2) A)),
           (w : CStarMatrix (Fin 2) (Fin 2) A) = cornerDiag A 2 (u : A)) := by
  sorry

end

end ProblemLIX
