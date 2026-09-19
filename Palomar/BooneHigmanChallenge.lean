/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.RingQuot
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Boone–Higman: embeddings in finitely presented simple groups, and related printed questions

**Work in progress.** Each theorem below answers a printed open question. The solution
module proves them from propositions the development has not yet discharged.

* `explicit_fp_overgroup_of_all_gl_n_q`: Kourovka Notebook Problem 14.10(c)
  (P. de la Harpe), also Problem 2.7 of Belk–Bleak–Matucci–Zaremsky, *Progress around the
  Boone–Higman conjecture*, arXiv:2306.16356v3. It asks for an explicit finitely presented
  group containing `GL_n(ℚ)`. The answer is the Steinberg group `St_10(R_L)` of an explicit
  ring `R_L` with six generators and nine relations, which contains every `GL_n(ℚ)` at once.
* `finitely_presented_metabelian_embeds_in_finitely_presented_simple`: item (7) of Problem 5.3
  of the same survey. `finitely_generated_metabelian_embeds_in_finitely_presented_simple` is
  its finitely generated form.
* `finitely_generated_linear_embeds_in_finitely_presented_simple`: every finitely generated
  linear group over any field embeds in a finitely presented simple group.
* `finitely_generated_linear_embeds_in_finitely_presented_self_similar`: Question 1.11 of
  Llosa Isenrich–Schesler–Wu, arXiv:2510.01952v1, asks whether every finitely generated
  linear group embeds in a finitely generated self-similar group. The answer is yes, even
  in a finitely presented one.
* `kourovka_17_59`: Kourovka Notebook Problem 17.59 (S. Kohl). Is Kohl's class transposition
  group `CT(ℤ)` exactly the group of residue-class-wise affine permutations of `ℤ` that
  fix the nonnegative integers setwise? The answer is yes.
* `kourovka_21_75`: Kourovka Notebook Problem 21.75 (S. Kohl). For sets `P₁`, `P₂` of odd
  primes, neither contained in the other, is `⟨CT_{P₁}(ℤ), CT_{P₂}(ℤ)⟩` a proper subgroup of
  `CT_{P₁ ∪ P₂}(ℤ)`? The answer is no: it is always all of it.
* `kohl_factorization_conjecture`: Kohl conjectures, in chapter 2 of the manual of his GAP
  package RCWA, that every residue-class-wise affine permutation of `ℤ` is a product of class
  shifts, class reflections and class transpositions. It is true.
* `exists_fp_simple_with_mixed_identities_not_finitely_normally_generated`: Question 3.3 of
  Belk–Fournier-Facio–Hyde–Zaremsky, arXiv:2503.21882v2, asks whether, for every finitely
  presented simple group `G`, the mixed identities `J_G(G ∗ F_n)` are finitely normally
  generated in `G ∗ F_n`. The answer is no.

Everything outside the shared block is Mathlib's vocabulary: `Group.IsFinitelyPresented`,
`Group.FG`, `Subgroup.FG`, `IsSimpleGroup`, `PresentedGroup`, `RingQuot`, `FreeAlgebra`,
`Monoid.Coprod` and `Subgroup.IsFinitelyNormallyGenerated`. All groups are quantified
over `Type`.

The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`. The prose of this
module was written by Claude (Anthropic), under the user's direction.
-/

namespace BooneHigman

-- BEGIN SHARED BLOCK (kept byte-identical in `Palomar/BooneHigmanChallenge.lean` and `Palomar/BooneHigmanSolution.lean`)

/-- A group is metabelian when its second derived subgroup `⁅G', G'⁆` is trivial. -/
def IsMetabelianGroup (G : Type) [Group G] : Prop :=
  ⁅commutator G, commutator G⁆ = ⊥

/-- `G` embeds into some finitely presented simple group. -/
def EmbedsInFinitelyPresentedSimpleGroup (G : Type) [Group G] : Prop :=
  ∃ (S : Type) (_ : Group S), Group.IsFinitelyPresented S ∧ IsSimpleGroup S ∧
    ∃ f : G →* S, Function.Injective f

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

/-- `S` is a self-similar group of automorphisms of the rooted `d`-ary tree `List (Fin d)`:
each element preserves lengths, and for every element `g` and vertex `v` there is `h` in `S`
with `g (v ++ w) = g v ++ h w` for all `w`. -/
def IsSelfSimilar {d : ℕ} (S : Subgroup (Equiv.Perm (List (Fin d)))) : Prop :=
  ∀ g ∈ S, (∀ v : List (Fin d), (g v).length = v.length) ∧
    ∀ v : List (Fin d), ∃ h ∈ S, ∀ w : List (Fin d), g (v ++ w) = g v ++ h w

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

/-- The mixed identities `J_G(G ∗ F_n)`: the intersection of the kernels of all
homomorphisms `G ∗ F_n → G` that restrict to the identity on `G`. -/
def mixedIdentities (G : Type) [Group G] (n : ℕ) :
    Subgroup (Monoid.Coprod G (FreeGroup (Fin n))) :=
  ⨅ (φ : Monoid.Coprod G (FreeGroup (Fin n)) →* G)
    (_ : φ.comp Monoid.Coprod.inl = MonoidHom.id G), φ.ker

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

-- END SHARED BLOCK

/-- **Kourovka 14.10(c), BBMZ Problem 2.7**: the explicit finitely presented group
`St_10(R_L)` contains every `GL_n(ℚ)`. -/
theorem explicit_fp_overgroup_of_all_gl_n_q :
    Group.IsFinitelyPresented (SteinbergGroup 10 LeavittResolventRing) ∧
      ∀ n : ℕ, ∃ f : Matrix.GeneralLinearGroup (Fin n) ℚ →*
        SteinbergGroup 10 LeavittResolventRing, Function.Injective f := by
  sorry

/-- **BBMZ Problem 5.3(7)**: every finitely presented metabelian group embeds in a
finitely presented simple group. -/
theorem finitely_presented_metabelian_embeds_in_finitely_presented_simple :
    ∀ (G : Type) [Group G], Group.IsFinitelyPresented G → IsMetabelianGroup G →
      EmbedsInFinitelyPresentedSimpleGroup G := by
  sorry

/-- The finitely generated form of BBMZ Problem 5.3(7). -/
theorem finitely_generated_metabelian_embeds_in_finitely_presented_simple :
    ∀ (G : Type) [Group G], Group.FG G → IsMetabelianGroup G →
      EmbedsInFinitelyPresentedSimpleGroup G := by
  sorry

/-- Every finitely generated linear group, over any field, embeds in a finitely presented
simple group. -/
theorem finitely_generated_linear_embeds_in_finitely_presented_simple :
    ∀ (K : Type) [Field K] (n : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)),
      H.FG →
      EmbedsInFinitelyPresentedSimpleGroup H := by
  sorry

/-- **Llosa Isenrich–Schesler–Wu, Question 1.11**: every finitely generated linear group,
over any field, embeds in a finitely presented self-similar group. -/
theorem finitely_generated_linear_embeds_in_finitely_presented_self_similar :
    ∀ (K : Type) [Field K] (n : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)),
      H.FG →
      ∃ (d : ℕ) (S : Subgroup (Equiv.Perm (List (Fin d)))), IsSelfSimilar S ∧
        Group.IsFinitelyPresented S ∧ ∃ f : H →* S, Function.Injective f := by
  sorry

/-- **Kourovka 17.59**: `CT(ℤ)` is exactly the group of residue-class-wise affine
permutations of `ℤ` that fix the nonnegative integers setwise. -/
theorem kourovka_17_59 :
    (classTranspositionGroup : Set (Equiv.Perm ℤ)) =
      {g | IsResidueClassWiseAffine g ∧ ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n} := by
  sorry

/-- **Kourovka 21.75, answered negatively**: for any two sets `P₁` and `P₂` of odd primes,
`CT_{P₁}(ℤ)` and `CT_{P₂}(ℤ)` generate `CT_{P₁ ∪ P₂}(ℤ)`, so the inclusion is never proper. -/
theorem kourovka_21_75 :
    ∀ P₁ P₂ : Set ℕ, (∀ p ∈ P₁, p.Prime ∧ p ≠ 2) → (∀ p ∈ P₂, p.Prime ∧ p ≠ 2) →
      classTranspositionGroupOver P₁ ⊔ classTranspositionGroupOver P₂ =
        classTranspositionGroupOver (P₁ ∪ P₂) := by
  sorry

/-- **Kohl's factorization conjecture** (RCWA package manual, chapter 2): the
residue-class-wise affine permutations of `ℤ` are exactly the products of class shifts,
class reflections and class transpositions. -/
theorem kohl_factorization_conjecture :
    {g : Equiv.Perm ℤ | IsResidueClassWiseAffine g} =
      (Subgroup.closure {g | IsClassShift g ∨ IsClassReflection g ∨ IsClassTransposition g} :
        Set (Equiv.Perm ℤ)) := by
  sorry

/-- **BFFHZ Question 3.3, answered negatively**: some finitely presented simple group has
mixed identities that are not finitely normally generated. -/
theorem exists_fp_simple_with_mixed_identities_not_finitely_normally_generated :
    ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ IsSimpleGroup G ∧
      ∃ n : ℕ, ¬ (mixedIdentities G n).IsFinitelyNormallyGenerated := by
  sorry

end BooneHigman
