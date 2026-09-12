/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.PathConnected
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIXStrong

/-!
# Proof of the strengthened STW Problem LIX theorems

The algebra is `GroupApproximation.LIX.Gen.LIXLimit n`, the inductive limit of the STW LIX
tower at rank `n`: corners of matrices over `C(X, ℂ)` with `X = S^{2n} × ∏ ℂP^{2ⁱ·n}`.  The
development proves it separable, C⋆-simple and nontrivial at every rank, and
`Manuscript/NinetyNineProblems/ProblemLIXStrong.lean` assembles those with the power witness
into the three statements this file translates into the challenge's vocabulary.

## What this file still owes

The three theorems the configuration selects are not here yet, and this file says so rather
than spelling them with a `sorry`.  What is here is each of them with one hypothesis in front,
`GroupApproximation.NinetyNineProblems.ClimbedPowersOutside n`: the `k`-indexed Corollary 4 at
the limit, which is `sp-tower`'s deliverable.  Every other step of all three is proved.

So `Palomar/comparator-lix-strong.json` is not a submittable surface today, and
`scripts/check_palomar_submission.py` lists it as pending for exactly that reason.  The day
`ClimbedPowersOutside` becomes a theorem this file gains three one-line wrappers carrying the
challenge's signatures verbatim, the configuration moves from the pending list to the enforced
one, and nothing else changes.

The prose of this module was written by Claude Fable 5.1.
-/

namespace ProblemLIXStrong

noncomputable section

-- BEGIN SHARED BLOCK (kept byte-identical in `Palomar/LIXChallenge.lean` and `Palomar/LIXSolution.lean`)

/-- `diag (a, 1, …, 1)`: the `n × n` matrix over `A` whose top-left entry is
`a`, whose remaining diagonal entries are `1`, and whose off-diagonal entries
are `0`. -/
def cornerDiag (A : Type) [CStarAlgebra A] (n : ℕ) (a : A) :
    CStarMatrix (Fin n) (Fin n) A :=
  fun i j => if i = j then (if (i : ℕ) = 0 then a else 1) else 0

/-- `K₁`-injectivity of a unital C⋆-algebra `A`: the canonical homomorphism
`U(A)/U₀(A) → K₁(A)` is injective, where `U₀(A)` is the path component of `1`
in the unitary group.

`K₁(A)` is the direct limit of the groups `U(Mₙ(A))/U₀(Mₙ(A))` along the
stabilisation maps `u ↦ diag (u, 1)`, so the class of a unitary `u ∈ U(A)`
vanishes in `K₁(A)` iff `diag (u, 1, …, 1) ∈ U₀(Mₙ(A))` for some `n ≥ 1`.
So `A` is `K₁`-injective iff every unitary whose stabilisation is connected
to `1` in some `Mₙ(A)` is connected to `1` in `U(A)`, which is the definition
below.  The stabilised unitary is described by its underlying matrix, so the
statement does not include a proof of unitarity.

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

/-- The development's power witness, restated in the challenge's vocabulary.

Two translations happen here and neither is mathematics.  `unitaryComponentOne B` is
`Subgroup.pathComponentOne (unitary B)`, whose carrier is `pathComponent 1`, so the two
membership statements are the same by unfolding.  And `diagOne v` is the block sum `diag (v, 1)`
as an element of `unitary (M₂(A))`, whose underlying matrix is `cornerDiag A 2 v` entry by
entry, which `fin_cases` checks in four cases. -/
theorem powers_witness_of (A : Type) [CStarAlgebra A] (n : ℕ)
    (h : NinetyNineProblems.HasK1InjPowerWitness A n) :
    letI : PartialOrder A := CStarAlgebra.spectralOrder A
    letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
    letI : Fintype (Fin 2) := Fin.fintype 2
    ∃ v : unitary A,
      (∃ w ∈ pathComponent (1 : unitary (CStarMatrix (Fin 2) (Fin 2) A)),
         (w : CStarMatrix (Fin 2) (Fin 2) A) = cornerDiag A 2 (v : A)) ∧
      ∀ k : ℕ, v ^ k ∈ pathComponent (1 : unitary A) →
        ∀ p : ℕ, p.Prime → p ∣ n → p ∣ k := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : Fintype (Fin 2) := Fin.fintype 2
  obtain ⟨v, hdiag, hpow⟩ := h
  refine ⟨v, ⟨diagOne v, hdiag, ?_⟩, fun k hk => hpow k hk⟩
  ext i j
  rw [coe_diagOne_apply]
  fin_cases i <;> fin_cases j <;> simp [cornerDiag]

/-- **The stronger theorem**, over the one proposition the construction still owes.

`ClimbedPowersOutside n` is `sp-tower`'s: one unitary of the rank-`n` limit whose stabilisation
is null-homotopic and whose `k`-th power stays outside `U₀` whenever a prime dividing `n` misses
`k`.  Everything else — nontriviality, simplicity, separability, and the exchange of the
contrapositive for the divisibility — is a theorem of the development. -/
theorem exists_simple_separable_powers_outside_U0_of (n : ℕ) (hn : 2 ≤ n)
    (hclimb : NinetyNineProblems.ClimbedPowersOutside n) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
      (letI : PartialOrder A := CStarAlgebra.spectralOrder A
       letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
       letI : Fintype (Fin 2) := Fin.fintype 2
       ∃ v : unitary A,
         (∃ w ∈ pathComponent (1 : unitary (CStarMatrix (Fin 2) (Fin 2) A)),
            (w : CStarMatrix (Fin 2) (Fin 2) A) = cornerDiag A 2 (v : A)) ∧
         ∀ k : ℕ, v ^ k ∈ pathComponent (1 : unitary A) →
           ∀ p : ℕ, p.Prime → p ∣ n → p ∣ k) := by
  obtain ⟨A, inst, hnt, hsimp, hsep, hwit⟩ :=
    NinetyNineProblems.exists_isSimpleRing_separable_hasK1InjPowerWitness_of n hn hclimb
  exact ⟨A, inst, hnt, hsimp, hsep, powers_witness_of A n hwit⟩

/-- **The `n = 6` instance**, over the same proposition at rank six.

The arithmetic step is `six_dvd_of_forall_prime_dvd`: `2 ∣ k` and `3 ∣ k` give `6 ∣ k` because
`2` and `3` are coprime. -/
theorem exists_simple_separable_order_six_witness_of
    (hclimb : NinetyNineProblems.ClimbedPowersOutside 6) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
      (letI : PartialOrder A := CStarAlgebra.spectralOrder A
       letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
       letI : Fintype (Fin 2) := Fin.fintype 2
       ∃ v : unitary A,
         (∃ w ∈ pathComponent (1 : unitary (CStarMatrix (Fin 2) (Fin 2) A)),
            (w : CStarMatrix (Fin 2) (Fin 2) A) = cornerDiag A 2 (v : A)) ∧
         ∀ k : ℕ, v ^ k ∈ pathComponent (1 : unitary A) → 6 ∣ k) := by
  obtain ⟨A, inst, hnt, hsimp, hsep, hwit⟩ :=
    exists_simple_separable_powers_outside_U0_of 6 (by norm_num) hclimb
  refine ⟨A, inst, hnt, hsimp, hsep, ?_⟩
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : Fintype (Fin 2) := Fin.fintype 2
  obtain ⟨v, hdiag, hpow⟩ := hwit
  exact ⟨v, hdiag, fun k hk =>
    NinetyNineProblems.six_dvd_of_forall_prime_dvd fun p hp hp6 => hpow k hk p hp hp6⟩

/-- **Every squarefree order**, over the same proposition at rank `N`.

The arithmetic step is `squarefree_dvd_of_forall_prime_dvd`: a squarefree `N` is the product of
its distinct prime factors, and a product of distinct primes divides `k` as soon as each factor
does. -/
theorem exists_simple_separable_squarefree_witness_of (N : ℕ) (hN : 2 ≤ N)
    (hsq : Squarefree N) (hclimb : NinetyNineProblems.ClimbedPowersOutside N) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
      (letI : PartialOrder A := CStarAlgebra.spectralOrder A
       letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
       letI : Fintype (Fin 2) := Fin.fintype 2
       ∃ v : unitary A,
         (∃ w ∈ pathComponent (1 : unitary (CStarMatrix (Fin 2) (Fin 2) A)),
            (w : CStarMatrix (Fin 2) (Fin 2) A) = cornerDiag A 2 (v : A)) ∧
         ∀ k : ℕ, v ^ k ∈ pathComponent (1 : unitary A) → N ∣ k) := by
  obtain ⟨A, inst, hnt, hsimp, hsep, hwit⟩ :=
    exists_simple_separable_powers_outside_U0_of N hN hclimb
  refine ⟨A, inst, hnt, hsimp, hsep, ?_⟩
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : Fintype (Fin 2) := Fin.fintype 2
  obtain ⟨v, hdiag, hpow⟩ := hwit
  exact ⟨v, hdiag, fun k hk =>
    NinetyNineProblems.squarefree_dvd_of_forall_prime_dvd hsq
      fun p hp hpN => hpow k hk p hp hpN⟩

end

end ProblemLIXStrong
