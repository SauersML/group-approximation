/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import GroupApproximation.BooneHigman.Statement.API
import GroupApproximation.GroupTheory.HydeLodha.HigmanInfiniteSimple

/-!
# Proofs for the Boone–Higman megasubmission (work in progress)

This file repeats the challenge's shared block byte for byte.

**Status: skeleton.** One theorem is proved outright:
`exists_finitely_presented_infinite_simple`, which is the development's theorem
`GroupApproximation.HydeLodha.higman_infinite_simple` (Hyde–Lodha's `Q₂`).
Every other selected theorem appears under a name ending `_of` and takes, as a hypothesis,
the proposition the development still owes:

* the two metabelian theorems and the linear theorem take the development endpoints
  `GroupApproximation.BooneHigman.FinitelyGeneratedMetabelianStatement` and
  `GroupApproximation.BooneHigman.FinitelyGeneratedLinearStatement`;
* the others take a proposition named here (`ExplicitOvergroupOwed`, `LinearSelfSimilarOwed`,
  `Kourovka1759Owed`, `MixedIdentitiesOwed`), which is the challenge statement itself until the
  construction that proves it lands.

The unsuffixed theorems that `Palomar/comparator-boone-higman.json` selects are added, and the
hypotheses removed, as the development discharges them.

**Where each owed proposition stands.**
* The metabelian and linear endpoints wait on the development's open gap statements; a wiring
  file stating them from those gaps is being written, and its `_of` forms will replace the
  endpoint hypotheses here.
* `ExplicitOvergroupOwed` needs finite presentation of Steinberg groups of finitely presented
  rings in rank at least five, the ring `R_L` with a faithful module, and the Leavitt-pair
  embedding of every `GL_n(ℚ)` into `St_10(R_L)`.
* `Kourovka1759Owed`: the answer currently rests on the identification of the class
  transposition groups with full groups of one-vertex higher-rank graphs, and through it on
  Matui's and Li's groupoid theorems. An elementary proof by products of class transpositions
  is in progress and is not yet complete.
* `MixedIdentitiesOwed`: the witness is Thompson's group `T`.

**Deferred candidates**, not yet in the configuration: the exceptional spherical Artin groups;
BFFHZ Question 3.1 (graph products of groups in the permutational class); Kourovka 17.60 and
17.61; and Zaremsky's Oberwolfach 2018 question on Higman's group in Lodha–Moore and Monod
groups.

The prose of this module was written by Claude (Anthropic), under the user's direction.
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

-- END SHARED BLOCK

/-- The challenge's metabelian groups are the development's. -/
theorem isMetabelianGroup_iff {G : Type} [Group G] :
    IsMetabelianGroup G ↔ GroupApproximation.BooneHigman.IsMetabelianGroup G :=
  Iff.rfl

/-- The challenge's embeddings in finitely presented simple groups are the development's. -/
theorem embedsInFinitelyPresentedSimpleGroup_iff {G : Type} [Group G] :
    EmbedsInFinitelyPresentedSimpleGroup G ↔
      GroupApproximation.BooneHigman.EmbedsInFinitelyPresentedSimpleGroup G :=
  Iff.rfl

/-- The proposition the Steinberg development owes for Kourovka 14.10(c). -/
def ExplicitOvergroupOwed : Prop :=
  Group.IsFinitelyPresented (SteinbergGroup 10 LeavittResolventRing) ∧
    ∀ n : ℕ, ∃ f : Matrix.GeneralLinearGroup (Fin n) ℚ →*
      SteinbergGroup 10 LeavittResolventRing, Function.Injective f

/-- Kourovka 14.10(c), from the proposition the Steinberg development owes. -/
theorem explicit_fp_overgroup_of_all_gl_n_q_of (h : ExplicitOvergroupOwed) :
    Group.IsFinitelyPresented (SteinbergGroup 10 LeavittResolventRing) ∧
      ∀ n : ℕ, ∃ f : Matrix.GeneralLinearGroup (Fin n) ℚ →*
        SteinbergGroup 10 LeavittResolventRing, Function.Injective f :=
  h

/-- The finitely generated metabelian form, from the development endpoint. -/
theorem finitely_generated_metabelian_embeds_in_finitely_presented_simple_of
    (h : GroupApproximation.BooneHigman.FinitelyGeneratedMetabelianStatement) :
    ∀ (G : Type) [Group G], Group.FG G → IsMetabelianGroup G →
      EmbedsInFinitelyPresentedSimpleGroup G := by
  intro G _ hfg hmet
  exact embedsInFinitelyPresentedSimpleGroup_iff.mpr (h G hfg (isMetabelianGroup_iff.mp hmet))

/-- BBMZ Problem 5.3(7), from the same endpoint: a finitely presented group is finitely
generated. -/
theorem finitely_presented_metabelian_embeds_in_finitely_presented_simple_of
    (h : GroupApproximation.BooneHigman.FinitelyGeneratedMetabelianStatement) :
    ∀ (G : Type) [Group G], Group.IsFinitelyPresented G → IsMetabelianGroup G →
      EmbedsInFinitelyPresentedSimpleGroup G := by
  intro G _ hfp hmet
  exact embedsInFinitelyPresentedSimpleGroup_iff.mpr
    (GroupApproximation.BooneHigman.finitelyPresentedMetabelianStatement_of_finitelyGenerated h
      G hfp (isMetabelianGroup_iff.mp hmet))

/-- Finitely generated linear groups, from the development endpoint. -/
theorem finitely_generated_linear_embeds_in_finitely_presented_simple_of
    (h : GroupApproximation.BooneHigman.FinitelyGeneratedLinearStatement) :
    ∀ (K : Type) [Field K] (n : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)),
      H.FG →
      EmbedsInFinitelyPresentedSimpleGroup H := by
  intro K _ n H hfg
  exact embedsInFinitelyPresentedSimpleGroup_iff.mpr (h K n H hfg)

/-- The proposition the linear development owes for Llosa Isenrich–Schesler–Wu Question 1.11. -/
def LinearSelfSimilarOwed : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)),
    H.FG →
    ∃ (d : ℕ) (S : Subgroup (Equiv.Perm (List (Fin d)))), IsSelfSimilar S ∧
      Group.IsFinitelyPresented S ∧ ∃ f : H →* S, Function.Injective f

/-- Llosa Isenrich–Schesler–Wu Question 1.11, from the proposition the linear development
owes. -/
theorem finitely_generated_linear_embeds_in_finitely_presented_self_similar_of
    (h : LinearSelfSimilarOwed) :
    ∀ (K : Type) [Field K] (n : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)),
      H.FG →
      ∃ (d : ℕ) (S : Subgroup (Equiv.Perm (List (Fin d)))), IsSelfSimilar S ∧
        Group.IsFinitelyPresented S ∧ ∃ f : H →* S, Function.Injective f :=
  h

/-- A finitely presented infinite simple group: Hyde–Lodha's `Q₂`, through
`GroupApproximation.HydeLodha.higman_infinite_simple`, which states the same proposition. -/
theorem exists_finitely_presented_infinite_simple :
    ∃ (n : ℕ) (rels : Set (FreeGroup (Fin n))), rels.Finite ∧
      IsSimpleGroup (PresentedGroup rels) ∧ Infinite (PresentedGroup rels) :=
  GroupApproximation.HydeLodha.higman_infinite_simple

/-- The same statement under its `_of` name; no hypothesis is outstanding. -/
theorem exists_finitely_presented_infinite_simple_of :
    ∃ (n : ℕ) (rels : Set (FreeGroup (Fin n))), rels.Finite ∧
      IsSimpleGroup (PresentedGroup rels) ∧ Infinite (PresentedGroup rels) :=
  exists_finitely_presented_infinite_simple

/-- The proposition the class-transposition development owes for Kourovka 17.59. -/
def Kourovka1759Owed : Prop :=
  (classTranspositionGroup : Set (Equiv.Perm ℤ)) =
    {g | IsResidueClassWiseAffine g ∧ ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n}

/-- Kourovka 17.59, from the proposition the class-transposition development owes. -/
theorem kourovka_17_59_of (h : Kourovka1759Owed) :
    (classTranspositionGroup : Set (Equiv.Perm ℤ)) =
      {g | IsResidueClassWiseAffine g ∧ ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n} :=
  h

/-- The proposition the mixed-identities development owes for BFFHZ Question 3.3. -/
def MixedIdentitiesOwed : Prop :=
  ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ IsSimpleGroup G ∧
    ∃ n : ℕ, ¬ (mixedIdentities G n).IsFinitelyNormallyGenerated

/-- BFFHZ Question 3.3, answered negatively, from the proposition the development owes. -/
theorem exists_fp_simple_with_mixed_identities_not_finitely_normally_generated_of
    (h : MixedIdentitiesOwed) :
    ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ IsSimpleGroup G ∧
      ∃ n : ℕ, ¬ (mixedIdentities G n).IsFinitelyNormallyGenerated :=
  h

end BooneHigman
