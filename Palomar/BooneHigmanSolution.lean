/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.RingQuot
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import GroupApproximation.SteinbergFP.Challenge
import GroupApproximation.Kourovka1759.Main
import GroupApproximation.KohlFactorization.Main
import GroupApproximation.Kourovka2175.Main

/-!
# Proofs for the Boone–Higman megasubmission (stage 1)

This file repeats the challenge's shared block byte for byte, then proves each selected theorem
from the development. Each development theorem is stated over byte-identical copies of the
shared definitions it uses, so it closes the challenge statement by definitional unfolding:

* `explicit_fp_overgroup_of_all_gl_n_q` (Kourovka 14.10(c)), from
  `GroupApproximation.SteinbergFP.explicit_fp_overgroup_of_all_gl_n_q`;
* `kourovka_17_59`, from `GroupApproximation.Kourovka1759.kourovka_17_59`;
* `kourovka_21_75`, from `GroupApproximation.Kourovka2175.kourovka_21_75`;
* `kohl_factorization_conjecture`, from
  `GroupApproximation.KohlFactorization.kohl_factorization_conjecture`.

**Review status of the mathematics** (research/artifacts/gq-bh-results-summary.md; [R] is an
internal referee pass, [IC] an adversarial check by a second lane; none is an external review):
Kourovka 14.10(c) [R], Kourovka 17.59 [IC], Kourovka 21.75 [R], Kohl's factorization
conjecture [R].

**Stage 2**, to be added when its inputs are proved: the metabelian and linear embeddings into
finitely presented simple groups (BBMZ Problem 5.3(7)) and LISW Question 1.11. They reduce, in
`GroupApproximation/BooneHigmanLinear/FrontierFour.lean` and
`GroupApproximation/BHPalomar/LinearSelfSimilar.lean`, to route A's inputs, among them the
vanishing of stable `K₂` of polynomial rings over `𝔽_p`. Kourovka 17.61 (its finite presentation
of `CT_P(ℤ)` by position shifting is refereed and being formalized) and BFFHZ Question 3.3 join
stage 1 when their Lean proofs close. BFFHZ Question 3.1 and Kourovka 17.57 and 17.60 are out
until the developments they need (twisted Brin–Thompson groups, Matui's and Rubin's spatial
realization, Adamczewski–Bell) exist.

The prose of this module was written by Claude (Anthropic), under the user's direction.
-/

namespace BooneHigman

-- BEGIN SHARED BLOCK (kept byte-identical in `Palomar/BooneHigmanChallenge.lean` and `Palomar/BooneHigmanSolution.lean`)

/-- The generators `s₁, s₂, t₁, t₂, N, A` of `R_L`, numbered `0, …, 5`. -/
def leavittResolventGenerator (i : Fin 6) : FreeAlgebra ℤ (Fin 6) :=
  FreeAlgebra.ι ℤ i

/-- The nine defining relations of `R_L`: `tᵢ sⱼ = δᵢⱼ`, `s₁ t₁ + s₂ t₂ = 1`,
`N s₁ = s₁ (N + 1)`, `N s₂ = 0` and `A (N + 1) = 1 = (N + 1) A`. -/
def leavittResolventRelation (a b : FreeAlgebra ℤ (Fin 6)) : Prop :=
  let s₁ := leavittResolventGenerator 0
  let s₂ := leavittResolventGenerator 1
  let t₁ := leavittResolventGenerator 2
  let t₂ := leavittResolventGenerator 3
  let N := leavittResolventGenerator 4
  let A := leavittResolventGenerator 5
  (a, b) ∈ ({(t₁ * s₁, 1), (t₁ * s₂, 0), (t₂ * s₁, 0), (t₂ * s₂, 1),
    (s₁ * t₁ + s₂ * t₂, 1), (N * s₁, s₁ * (N + 1)), (N * s₂, 0), (A * (N + 1), 1),
    ((N + 1) * A, 1)} : Set (FreeAlgebra ℤ (Fin 6) × FreeAlgebra ℤ (Fin 6)))

/-- The ring `R_L = ℤ⟨s₁, s₂, t₁, t₂, N, A⟩` modulo the nine relations above. -/
abbrev LeavittResolventRing : Type :=
  RingQuot leavittResolventRelation

/-- The Steinberg relations on the symbols `x_ij(r)`: `x_ii(r) = 1`,
`x_ij(r) x_ij(s) = x_ij(r + s)`, `[x_ij(r), x_jk(s)] = x_ik(r s)` for distinct `i, j, k`,
and `[x_ij(r), x_kl(s)] = 1` for `i ≠ j`, `k ≠ l`, `j ≠ k`, `i ≠ l`. -/
def steinbergRelations (n : ℕ) (R : Type) [Ring R] : Set (FreeGroup (Fin n × Fin n × R)) :=
  {w | (∃ (i : Fin n) (r : R), w = FreeGroup.of (i, i, r)) ∨
    (∃ (i j : Fin n) (r s : R),
      w = FreeGroup.of (i, j, r) * FreeGroup.of (i, j, s) * (FreeGroup.of (i, j, r + s))⁻¹) ∨
    (∃ (i j k : Fin n) (r s : R), i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      w = FreeGroup.of (i, j, r) * FreeGroup.of (j, k, s) * (FreeGroup.of (i, j, r))⁻¹ *
        (FreeGroup.of (j, k, s))⁻¹ * (FreeGroup.of (i, k, r * s))⁻¹) ∨
    (∃ (i j k l : Fin n) (r s : R), i ≠ j ∧ k ≠ l ∧ j ≠ k ∧ i ≠ l ∧
      w = FreeGroup.of (i, j, r) * FreeGroup.of (k, l, s) * (FreeGroup.of (i, j, r))⁻¹ *
        (FreeGroup.of (k, l, s))⁻¹)}

/-- The Steinberg group `St_n(R)`. -/
abbrev SteinbergGroup (n : ℕ) (R : Type) [Ring R] : Type :=
  PresentedGroup (steinbergRelations n R)

/-- `g` is Kohl's class transposition of two disjoint residue classes `r₁ + m₁ℤ` and
`r₂ + m₂ℤ` (with `0 ≤ rᵢ < mᵢ`): it maps `r₁ + t m₁ ↦ r₂ + t m₂` and back, and fixes
every other integer. -/
def IsClassTransposition (g : Equiv.Perm ℤ) : Prop :=
  ∃ r₁ m₁ r₂ m₂ : ℤ, 0 ≤ r₁ ∧ r₁ < m₁ ∧ 0 ≤ r₂ ∧ r₂ < m₂ ∧
    (∀ t₁ t₂ : ℤ, r₁ + t₁ * m₁ ≠ r₂ + t₂ * m₂) ∧
    (∀ t : ℤ, g (r₁ + t * m₁) = r₂ + t * m₂ ∧
      g (r₂ + t * m₂) = r₁ + t * m₁) ∧
    ∀ n : ℤ, (∀ t : ℤ, n ≠ r₁ + t * m₁) → (∀ t : ℤ, n ≠ r₂ + t * m₂) →
      g n = n

/-- Kohl's group `CT(ℤ)`, generated by the class transpositions. -/
def classTranspositionGroup : Subgroup (Equiv.Perm ℤ) :=
  Subgroup.closure {g | IsClassTransposition g}

/-- `g` is residue-class-wise affine: for some modulus `m ≥ 1`, on each residue class
`r + mℤ` it is `n ↦ (a n + b) / c` for integers `a, b, c` with `c ≠ 0`. -/
def IsResidueClassWiseAffine (g : Equiv.Perm ℤ) : Prop :=
  ∃ m : ℤ, 0 < m ∧ ∀ r : ℤ, ∃ a b c : ℤ, c ≠ 0 ∧
    ∀ t : ℤ, c * g (r + t * m) = a * (r + t * m) + b

/-- `g` is Kohl's class shift `ν_{r(m)}`: it maps `r + t m ↦ r + (t + 1) m` for every `t` and
fixes every integer outside `r(m)`. -/
def IsClassShift (g : Equiv.Perm ℤ) : Prop :=
  ∃ r m : ℤ, 0 ≤ r ∧ r < m ∧ (∀ t : ℤ, g (r + t * m) = r + t * m + m) ∧
    ∀ n : ℤ, (∀ t : ℤ, n ≠ r + t * m) → g n = n

/-- `g` is Kohl's class reflection `ς_{r(m)}`: it maps `r + t m ↦ r - t m`, that is
`n ↦ -n + 2r` on `r(m)`, and fixes every integer outside `r(m)`. -/
def IsClassReflection (g : Equiv.Perm ℤ) : Prop :=
  ∃ r m : ℤ, 0 ≤ r ∧ r < m ∧ (∀ t : ℤ, g (r + t * m) = r - t * m) ∧
    ∀ n : ℤ, (∀ t : ℤ, n ≠ r + t * m) → g n = n

/-- `m` has no prime factor outside `P ∪ {2}`. -/
def IsSmoothModulus (P : Set ℕ) (m : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → p = 2 ∨ p ∈ P

/-- `g` is a class transposition (as in `IsClassTransposition`) of two residue classes whose
moduli have only prime factors in `P ∪ {2}`. -/
def IsClassTranspositionOver (P : Set ℕ) (g : Equiv.Perm ℤ) : Prop :=
  ∃ r₁ m₁ r₂ m₂ : ℤ, IsSmoothModulus P m₁ ∧ IsSmoothModulus P m₂ ∧
    0 ≤ r₁ ∧ r₁ < m₁ ∧ 0 ≤ r₂ ∧ r₂ < m₂ ∧
    (∀ t₁ t₂ : ℤ, r₁ + t₁ * m₁ ≠ r₂ + t₂ * m₂) ∧
    (∀ t : ℤ, g (r₁ + t * m₁) = r₂ + t * m₂ ∧
      g (r₂ + t * m₂) = r₁ + t * m₁) ∧
    ∀ n : ℤ, (∀ t : ℤ, n ≠ r₁ + t * m₁) → (∀ t : ℤ, n ≠ r₂ + t * m₂) →
      g n = n

/-- Kohl's group `CT_P(ℤ)`, generated by the class transpositions over `P`. -/
def classTranspositionGroupOver (P : Set ℕ) : Subgroup (Equiv.Perm ℤ) :=
  Subgroup.closure {g | IsClassTranspositionOver P g}

-- END SHARED BLOCK

/-- **Kourovka 14.10(c), BBMZ Problem 2.7**: the explicit finitely presented group
`St_10(R_L)` contains every `GL_n(ℚ)`. The development's theorem is stated over byte-identical
copies of `R_L`, the Steinberg relations and `St_n`. -/
theorem explicit_fp_overgroup_of_all_gl_n_q :
    Group.IsFinitelyPresented (SteinbergGroup 10 LeavittResolventRing) ∧
      ∀ n : ℕ, ∃ f : Matrix.GeneralLinearGroup (Fin n) ℚ →*
        SteinbergGroup 10 LeavittResolventRing, Function.Injective f :=
  GroupApproximation.SteinbergFP.explicit_fp_overgroup_of_all_gl_n_q

/-- **Kourovka 17.59** (lane bh-pal-kourovka59): `CT(ℤ)` is exactly the group of
residue-class-wise affine permutations of `ℤ` that fix the nonnegative integers setwise. -/
theorem kourovka_17_59 :
    (classTranspositionGroup : Set (Equiv.Perm ℤ)) =
      {g | IsResidueClassWiseAffine g ∧ ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n} :=
  GroupApproximation.Kourovka1759.kourovka_17_59

/-- **Kourovka 21.75, answered negatively** (lane pal-k2175): for any two sets `P₁` and `P₂` of
odd primes, `CT_{P₁}(ℤ)` and `CT_{P₂}(ℤ)` generate `CT_{P₁ ∪ P₂}(ℤ)`, so the inclusion is never
proper. -/
theorem kourovka_21_75 :
    ∀ P₁ P₂ : Set ℕ, (∀ p ∈ P₁, p.Prime ∧ p ≠ 2) → (∀ p ∈ P₂, p.Prime ∧ p ≠ 2) →
      classTranspositionGroupOver P₁ ⊔ classTranspositionGroupOver P₂ =
        classTranspositionGroupOver (P₁ ∪ P₂) :=
  GroupApproximation.Kourovka2175.kourovka_21_75

/-- **Kohl's factorization conjecture** (lane pal-kohl): the residue-class-wise affine
permutations of `ℤ` are exactly the products of class shifts, class reflections and class
transpositions. -/
theorem kohl_factorization_conjecture :
    {g : Equiv.Perm ℤ | IsResidueClassWiseAffine g} =
      (Subgroup.closure {g | IsClassShift g ∨ IsClassReflection g ∨ IsClassTransposition g} :
        Set (Equiv.Perm ℤ)) :=
  GroupApproximation.KohlFactorization.kohl_factorization_conjecture

end BooneHigman
