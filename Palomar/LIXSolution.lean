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
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIX

/-!
# Proof of the STW Problem LIX theorems

The counterexample is `GroupApproximation.LIX.LIXLimit`, the inductive limit of
the STW LIX tower of corner algebras of matrices over `C(X, ℂ)`.  The
development proves it separable (`LIX.lixLimit_separableSpace`), C⋆-simple
(`LIX.lixLimit_isSimpleCStar`, converted to Mathlib's `IsSimpleRing` by
`isSimpleCStar_iff_isSimpleRing`), and carrying a unitary `u ∉ U₀(A)` with
`diag (u, 1) ∈ U₀(M₂(A))` (`LIX.lixLimit_hasK1InjWitness_of` at
`CharClass.lemmaTwoHolds`, the mod-2 Gysin identity).  The three compared
theorems are assembled from those facts and nothing else.
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
vanishes in `K₁(A)` exactly when `diag (u, 1, …, 1) ∈ U₀(Mₙ(A))` for some
`n ≥ 1`, and a group homomorphism is injective exactly when its kernel is
trivial.  The definition records precisely that: every unitary of `A` whose
stabilisation is connected to `1` in some matrix algebra over `A` is already
connected to `1` in `U(A)`.  `U₀` is written as `pathComponent 1`, the path
component of `1` in the unitary group with its norm topology; the stabilised
unitary is described by its underlying matrix, so that no unitarity proof has
to be packaged inside the statement.

Mathlib's C⋆-structure on `Mₙ(A)`, `CStarMatrix.instCStarAlgebra`, asks for a
partial order on `A` making it a `StarOrderedRing`.  A unital C⋆-algebra has
exactly one such order, the spectral order (`x ≤ y` iff `y - x` is positive),
and that is the one supplied. -/
def IsK1Injective (A : Type) [CStarAlgebra A] : Prop :=
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  ∀ u : unitary A,
    (∃ n : ℕ, 0 < n ∧
      ∃ w ∈ pathComponent (1 : unitary (CStarMatrix (Fin n) (Fin n) A)),
        (w : CStarMatrix (Fin n) (Fin n) A) = cornerDiag A n (u : A)) →
    u ∈ pathComponent (1 : unitary A)

-- END SHARED BLOCK

open GroupApproximation

/-- The development's witness, restated in the challenge's vocabulary: at the
counterexample algebra there is a unitary outside `U₀(A)` whose `diag (u, 1)`,
as a matrix, is the underlying matrix of an element of `U₀(M₂(A))`. -/
theorem lixLimit_stage_two_witness :
    letI : PartialOrder LIX.LIXLimit := CStarAlgebra.spectralOrder LIX.LIXLimit
    letI : StarOrderedRing LIX.LIXLimit := CStarAlgebra.spectralOrderedRing LIX.LIXLimit
    letI : Fintype (Fin 2) := Fin.fintype 2
    ∃ u : unitary LIX.LIXLimit, u ∉ pathComponent (1 : unitary LIX.LIXLimit) ∧
      ∃ w ∈ pathComponent (1 : unitary (CStarMatrix (Fin 2) (Fin 2) LIX.LIXLimit)),
        (w : CStarMatrix (Fin 2) (Fin 2) LIX.LIXLimit)
          = cornerDiag LIX.LIXLimit 2 (u : LIX.LIXLimit) := by
  letI : PartialOrder LIX.LIXLimit := CStarAlgebra.spectralOrder LIX.LIXLimit
  letI : StarOrderedRing LIX.LIXLimit := CStarAlgebra.spectralOrderedRing LIX.LIXLimit
  letI : Fintype (Fin 2) := Fin.fintype 2
  obtain ⟨u, hu, hdiag⟩ := LIX.lixLimit_hasK1InjWitness_of CharClass.lemmaTwoHolds
  -- `unitaryComponentOne B` is `Subgroup.pathComponentOne (unitary B)`, whose carrier is
  -- `pathComponent 1`; both memberships below are that carrier's, by unfolding.
  refine ⟨u, fun h => hu h, diagOne u, hdiag, ?_⟩
  ext i j
  rw [coe_diagOne_apply]
  fin_cases i <;> fin_cases j <;> simp [cornerDiag]

/-- A unitary that is not connected to `1` in `U(A)` but whose `diag (u, 1)`
is connected to `1` in `U(M₂(A))` refutes `K₁`-injectivity, with `n = 2`. -/
theorem not_isK1Injective_of_stage_two_witness (A : Type) [CStarAlgebra A]
    (h : letI : PartialOrder A := CStarAlgebra.spectralOrder A
         letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
         letI : Fintype (Fin 2) := Fin.fintype 2
         ∃ u : unitary A, u ∉ pathComponent (1 : unitary A) ∧
           ∃ w ∈ pathComponent (1 : unitary (CStarMatrix (Fin 2) (Fin 2) A)),
             (w : CStarMatrix (Fin 2) (Fin 2) A) = cornerDiag A 2 (u : A)) :
    ¬ IsK1Injective A := by
  intro hinj
  obtain ⟨u, hu, w, hw, heq⟩ := h
  exact hu (hinj u ⟨2, by norm_num, w, hw, heq⟩)

/-- **The sharp form**: a separable simple unital C⋆-algebra `A` carrying a
unitary `u` that is not connected to `1` in `U(A)`, although `diag (u, 1)` is
connected to `1` in `U(M₂(A))`.  The class of `u` therefore vanishes already at
the first stabilisation step, which refutes `K₁`-injectivity of `A` with `n = 2`
in `IsK1Injective`.  The `Fintype (Fin 2)` instance behind `M₂(A)` is pinned to
Mathlib's `Fin.fintype 2` so that the statement elaborates to the same term in
every environment, whatever other instances happen to be imported. -/
theorem exists_separable_simple_stage_two_witness :
    ∃ (A : Type) (_ : CStarAlgebra A),
      TopologicalSpace.SeparableSpace A ∧ IsSimpleRing A ∧
      (letI : PartialOrder A := CStarAlgebra.spectralOrder A
       letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
       letI : Fintype (Fin 2) := Fin.fintype 2
       ∃ u : unitary A, u ∉ pathComponent (1 : unitary A) ∧
         ∃ w ∈ pathComponent (1 : unitary (CStarMatrix (Fin 2) (Fin 2) A)),
           (w : CStarMatrix (Fin 2) (Fin 2) A) = cornerDiag A 2 (u : A)) :=
  ⟨LIX.LIXLimit, inferInstance, LIX.lixLimit_separableSpace,
    (isSimpleCStar_iff_isSimpleRing LIX.LIXLimit).mp LIX.lixLimit_isSimpleCStar,
    lixLimit_stage_two_witness⟩

/-- **The counterexample is separable**: there is a separable simple unital
C⋆-algebra that is not `K₁`-injective. -/
theorem exists_separable_simple_not_k1Injective :
    ∃ (A : Type) (_ : CStarAlgebra A),
      TopologicalSpace.SeparableSpace A ∧ IsSimpleRing A ∧ ¬ IsK1Injective A := by
  obtain ⟨A, inst, hsep, hsimp, hwit⟩ := exists_separable_simple_stage_two_witness
  exact ⟨A, inst, hsep, hsimp, not_isK1Injective_of_stage_two_witness A hwit⟩

/-- **STW Problem LIX has a negative answer**: it is not the case that every
nontrivial simple unital C⋆-algebra is `K₁`-injective. -/
theorem not_all_simple_unital_k1Injective :
    ¬ ∀ (A : Type) [CStarAlgebra A], Nontrivial A → IsSimpleRing A → IsK1Injective A := by
  intro hall
  obtain ⟨A, inst, _, hsimp, hnot⟩ := exists_separable_simple_not_k1Injective
  exact hnot (hall A inferInstance hsimp)

end

end ProblemLIX
