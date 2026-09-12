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

/-!
# STW Problem LIX, strengthened: unitaries of large order that vanish in `K₁`

Schafhauser, Tikuisis and White, *Nuclear C⋆-algebras: 99 problems*
(arXiv:2506.10902), print as Problem LIX, verbatim:

> Are all unital simple C*-algebras K1-injective?

`Palomar/LIXChallenge.lean` answers that question: there is a separable simple
unital C⋆-algebra `A` and a unitary `u ∈ U(A) \ U₀(A)` with `diag (u, 1)`
connected to `1` in `U(M₂(A))`, so the class of `u` in `U(A)/U₀(A)` is
nontrivial and dies at the first stabilisation.  A counterexample of that kind
says the kernel of `U(A)/U₀(A) → K₁(A)` is nonzero.  It says nothing about how
large that kernel is: one nontrivial element is all it exhibits.

The three theorems below say how large.  For every `n ≥ 2` there is such an
algebra carrying a unitary `v`, still trivial in `K₁`, whose powers stay
outside `U₀(A)` unless the exponent is divisible by every prime dividing `n`.
So the class of `v` in `U(A)/U₀(A)` has order divisible by the radical of `n`,
or infinite order, while still lying in the kernel of the map to `K₁(A)`.
Taking `n = 6` gives an element whose order is divisible by six; taking `n`
squarefree gives one whose order is divisible by `n`.

`v ∉ U₀(A)` is not a separate hypothesis or conclusion anywhere below.  It is
the power clause read at `k = 1`: some prime `p` divides `n`, because `2 ≤ n`,
and `p ∣ 1` is false for a prime.

## What is claimed and what is not

The order of `v` in `U(A)/U₀(A)` is not computed, and `K₁(A)` is not computed.
What is proved is a divisibility, a lower bound on the order that a mod-`p`
argument can see, and the statements say exactly that: an implication from
`v ^ k ∈ U₀(A)` to `p ∣ k`, for each prime `p ∣ n`.  In particular nothing
below asserts `K₁(A) = 0`, nor that the order of `v` is finite, nor that
`p² ∣ k`.

## Vocabulary

Every notion except the two definitions below is Mathlib's, and the block that
carries them is the one `Palomar/LIXChallenge.lean` and
`Palomar/LIXSolution.lean` carry, verbatim, so that the four files share one
copy a reader can diff.  `IsK1Injective` is therefore present and unused: none
of the three statements below mentions it, because each says something
strictly stronger than `¬ IsK1Injective A`, which follows from the power clause
at `k = 1` together with the stabilisation clause.

`CStarAlgebra A` is a *unital* C⋆-algebra (`CStarAlgebra` extends
`NormedRing`), so unitality is not a separate hypothesis.  `IsSimpleRing A` is
Mathlib's simplicity: the only two-sided ideals are `⊥` and `⊤`.  For a unital
C⋆-algebra this agrees with C⋆-simplicity (only the *closed* two-sided ideals
are asked about), because a proper two-sided ideal of a unital Banach algebra
misses a neighbourhood of `1` and so has proper closure.
`TopologicalSpace.SeparableSpace A` is separability.  `unitary A` is the
unitary group, `pathComponent (1 : unitary A)` is `U₀(A)`, `v ^ k` is the power
in that group, and `CStarMatrix (Fin n) (Fin n) A` is `Mₙ(A)` with Mathlib's
C⋆-norm.  All algebras are quantified over `Type`, where the counterexample
lives.

The rank `n` occurs in the statements only as a natural number, in `p ∣ n`.  It
is never a matrix index and never an index type, so no instance on `Fin n`
appears: the whole rank-`n` construction is on the solution side.

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

/-- **The stronger theorem.**  For every `n ≥ 2` there is a separable simple
unital C⋆-algebra carrying a unitary `v` whose stabilisation `diag (v, 1)` is
connected to `1` in `U(M₂(A))` — so its `K₁`-class dies at the first
stabilisation — and whose powers stay outside `U₀(A)` unless the exponent is
divisible by every prime dividing `n`.

Read at `k = 1` the power clause says `v ∉ U₀(A)`: `2 ≤ n` gives a prime `p`
dividing `n`, and a prime does not divide `1`.  So `v` is a nontrivial element
of `U(A)/U₀(A)` lying in the kernel of the map to `K₁(A)`, and the clause at
general `k` says its order there is divisible by every prime dividing `n`, or
is infinite.

The `Fintype (Fin 2)` instance is pinned to `Fin.fintype 2` so that the
statement elaborates to the same term in every environment; `n` occurs only as
a natural number, never as a matrix index, so no instance on `Fin n` is
involved. -/
theorem exists_simple_separable_powers_outside_U0 (n : ℕ) (hn : 2 ≤ n) :
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
  sorry

/-- **The `n = 6` instance.**  A separable simple unital C⋆-algebra with a
unitary whose class dies at the first stabilisation and whose powers leave
`U₀(A)` unless the exponent is divisible by `6`: an element of `U(A)/U₀(A)` of
order divisible by `6`, or of infinite order, that is trivial in `K₁`.

Six is the smallest number that is neither `1` nor a prime power, and that is
the point of the instance: the two primes are seen by two different mod-`p`
arguments at one algebra, which is what the mod-2 answer to Problem LIX could
not do. -/
theorem exists_simple_separable_order_six_witness :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
      (letI : PartialOrder A := CStarAlgebra.spectralOrder A
       letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
       letI : Fintype (Fin 2) := Fin.fintype 2
       ∃ v : unitary A,
         (∃ w ∈ pathComponent (1 : unitary (CStarMatrix (Fin 2) (Fin 2) A)),
            (w : CStarMatrix (Fin 2) (Fin 2) A) = cornerDiag A 2 (v : A)) ∧
         ∀ k : ℕ, v ^ k ∈ pathComponent (1 : unitary A) → 6 ∣ k) := by
  sorry

/-- **Every squarefree order is realised.**  For squarefree `N ≥ 2` there is a
separable simple unital C⋆-algebra with a unitary trivial in `K₁` whose powers
leave `U₀(A)` unless `N` divides the exponent.

Squarefree is exactly the hypothesis this method supports: mod-`p` cohomology
sees the prime `p` and not `p²`, so the conclusion the general theorem yields
at rank `n` is divisibility by the radical of `n`, and that is `n` itself
precisely when `n` is squarefree. -/
theorem exists_simple_separable_squarefree_witness (N : ℕ) (hN : 2 ≤ N)
    (hsq : Squarefree N) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
      (letI : PartialOrder A := CStarAlgebra.spectralOrder A
       letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
       letI : Fintype (Fin 2) := Fin.fintype 2
       ∃ v : unitary A,
         (∃ w ∈ pathComponent (1 : unitary (CStarMatrix (Fin 2) (Fin 2) A)),
            (w : CStarMatrix (Fin 2) (Fin 2) A) = cornerDiag A 2 (v : A)) ∧
         ∀ k : ℕ, v ^ k ∈ pathComponent (1 : unitary A) → N ∣ k) := by
  sorry

end

end ProblemLIXStrong
