/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.GroupTheory.PresentedGroup

/-!
# Guba's Question 3.20: the equation `(1 - x₁) u = b v` in the group ring of `F`

V. Guba, *Amenability problem for Thompson's group `F`: state of the art*, Groups Complexity
Cryptology 15:1 (2023), arXiv:2305.07113, prints Question 3.20 on p. 3:18, verbatim:

> Let R = K[F] be a group ring of F over a field K. Is it true that for any element b∈R, the
> equation (1−x1)u = bv has a non-zero solution in R?

The same question is Question 1 of V. Guba, arXiv:2201.02308.  Just before the question the
survey records that it was not known whether such equations have nontrivial solutions, while its
Theorem 3.18 gives a non-zero solution for every `b` with `1 - x₀` in place of `1 - x₁`.

The two theorems below answer **yes**:

* `question_3_20` is the question as printed: for every field `K` and every `b ∈ K[F]` the
  equation has a solution `(u, v)` with `u ≠ 0` or `v ≠ 0`;
* `question_3_20_common_multiple` is the Ore form for `b ≠ 0`: the common multiple `b v` is itself
  non-zero, so the right ideals `(1 - x₁) K[F]` and `b K[F]` meet in a non-zero element.

The second form does not rest on the absence of zero divisors.  At a zero divisor `b` the first
form would hold with `u = 0`.  `K[F]` has no zero divisors (the survey, p. 3:12), so over `F` the
two forms agree for `b ≠ 0`.

## Vocabulary

Every notion except the definitions in the shared block is Mathlib's.

* `ThompsonF` is Thompson's group `F` given by the survey's presentation (1.2) on p. 3:6,
  `⟨x₀, x₁ | x₁^(x₀²) = x₁^(x₀x₁), x₁^(x₀³) = x₁^(x₀²x₁)⟩`, where `a^b = b⁻¹ab` is `conjBy a b`.
  Each relation `u = v` enters `thompsonRels` as the relator `u * v⁻¹`.
* `x0` and `x1` are the images in `F` of the generators `x₀` and `x₁`.
* The group ring `K[F]` is `MonoidAlgebra K ThompsonF`, and the element `x₁` of `K[F]` is
  `MonoidAlgebra.of K ThompsonF x1`.
* A non-zero solution is a pair `(u, v)` with `u ≠ 0 ∨ v ≠ 0`.  This is the survey's own reading:
  on p. 3:12 the Ore condition asks for `u, v` with `au = bv` and `u ≠ 0` or `v ≠ 0`.

Fields range over every universe.

The prose of this module was written by Claude (Anthropic).
-/

namespace GubaThompson

noncomputable section

-- BEGIN SHARED BLOCK (kept byte-identical in `Palomar/GubaThompsonChallenge.lean` and `Palomar/GubaThompsonSolution.lean`)

/-- Guba's exponent notation `a^b = b⁻¹ab` (the survey, p. 3:6), in the free group on `x₀, x₁`. -/
def conjBy (a b : FreeGroup (Fin 2)) : FreeGroup (Fin 2) :=
  b⁻¹ * a * b

/-- The relators of presentation (1.2), `x₁^(x₀²) = x₁^(x₀x₁)` and `x₁^(x₀³) = x₁^(x₀²x₁)`, each
relation `u = v` written as `u * v⁻¹`, where `x₀ = FreeGroup.of 0` and `x₁ = FreeGroup.of 1`. -/
def thompsonRels : Set (FreeGroup (Fin 2)) :=
  {conjBy (FreeGroup.of 1) (FreeGroup.of 0 ^ 2) *
      (conjBy (FreeGroup.of 1) (FreeGroup.of 0 * FreeGroup.of 1))⁻¹,
    conjBy (FreeGroup.of 1) (FreeGroup.of 0 ^ 3) *
      (conjBy (FreeGroup.of 1) (FreeGroup.of 0 ^ 2 * FreeGroup.of 1))⁻¹}

/-- Thompson's group `F`, by presentation (1.2) of the survey. -/
abbrev ThompsonF : Type :=
  PresentedGroup thompsonRels

/-- The generator `x₀` of `F`. -/
def x0 : ThompsonF :=
  PresentedGroup.of 0

/-- The generator `x₁` of `F`. -/
def x1 : ThompsonF :=
  PresentedGroup.of 1

-- END SHARED BLOCK

/-- **Question 3.20 has a positive answer**: for every field `K` and every `b ∈ K[F]`, the
equation `(1 - x₁) u = b v` has a solution `(u, v) ≠ (0, 0)`. -/
theorem question_3_20 (K : Type*) [Field K] (b : MonoidAlgebra K ThompsonF) :
    ∃ u v : MonoidAlgebra K ThompsonF,
      (u ≠ 0 ∨ v ≠ 0) ∧ (1 - MonoidAlgebra.of K ThompsonF x1) * u = b * v := by
  sorry

/-- **The Ore form**: for every non-zero `b ∈ K[F]` the right ideals `(1 - x₁) K[F]` and
`b K[F]` meet in a non-zero element. -/
theorem question_3_20_common_multiple (K : Type*) [Field K]
    (b : MonoidAlgebra K ThompsonF) (hb : b ≠ 0) :
    ∃ u v : MonoidAlgebra K ThompsonF,
      b * v ≠ 0 ∧ (1 - MonoidAlgebra.of K ThompsonF x1) * u = b * v := by
  sorry

end

end GubaThompson
