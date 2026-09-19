/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.RingQuot
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import GroupApproximation.BooneHigman.Statement.API
import GroupApproximation.SteinbergFP.Challenge
import GroupApproximation.BooneHigmanLinear.FrontierFour

/-!
# Proofs for the Boone–Higman megasubmission (work in progress)

This file repeats the challenge's shared block byte for byte.

**Status.** `explicit_fp_overgroup_of_all_gl_n_q` (Kourovka 14.10(c)) is proved outright, from
`GroupApproximation.SteinbergFP.explicit_fp_overgroup_of_all_gl_n_q`; it is also available
under its `_of` name. Every other selected theorem appears under a name ending `_of` and takes,
as a hypothesis, the proposition the development still owes:

* the two metabelian theorems and the linear theorem take `RouteAOwed`, the four open inputs of
  route A (`GroupApproximation/BooneHigmanLinear/FrontierFour.lean`);
* the others take a proposition named here (`LinearSelfSimilarOwed`, `Kourovka1757Owed`,
  `Kourovka1759Owed`, `Kourovka1760Owed`, `Kourovka1761Owed`, `Kourovka2175Owed`,
  `KohlFactorizationOwed`, `GraphProductOwed`, `MixedIdentitiesOwed`), which is the challenge
  statement itself until the construction that proves it lands.

The unsuffixed theorems that `Palomar/comparator-boone-higman.json` selects are added, and the
hypotheses removed, as the development discharges them.

**Where each owed proposition stands.**
* `RouteAOwed`: route A reduces the metabelian and linear theorems to four named Statements of
  the metabelian chain (Suslin absorption at bad primes, the two `K₂` gaps, and the Higman–`V`
  step-B core); each is open in the development.
* `Kourovka1757Owed`: automorphisms of `CT(ℤ)` are spatial (Matui); a normalizing
  homeomorphism, after the reflection, restricts to a bijection of the nonnegative integers
  that is both 2-regular and 3-regular, hence affine on a residue class (Adamczewski–Bell).
* `Kourovka1759Owed`: the elementary proof by products of class transpositions is complete
  as a written argument; its Lean development is in progress.
* `Kourovka1760Owed`, `Kourovka1761Owed`: `CT_P(ℤ)` is the topological full group of an
  explicit one-vertex higher-rank graph, simple and of type `F_∞` by Li's theorems; Matui's
  spatial realization and the germ groups at rational points then recover `P`.
* `Kourovka2175Owed`: elementary, by transporting class transpositions through boxes of
  modulus four with products of class transpositions of the other group.
* `KohlFactorizationOwed`: from Kourovka 17.59, after removing class shifts and class
  reflections to fix the nonnegative integers.
* `GraphProductOwed`: graph products reduce to amalgams `X ∗_C (C × K)` over retracts, which a
  twisted conjugation realizes inside the automorphism groups `Aut_G(G ∗ F_n)` of BFFHZ.
* `MixedIdentitiesOwed`: the witness is Thompson's group `T`.

**Review status of the mathematics** (research/artifacts/gq-bh-results-summary.md; [R] is an
internal referee pass, [IC] an adversarial check by a second lane; none is an external review):
Kourovka 14.10(c) [R] and proved here in Lean; Kourovka 17.60, 21.75 and Kohl's
factorization conjecture [R]; Kourovka 17.57, 17.59 and 17.61, BFFHZ Questions 3.1 and 3.3,
the metabelian and linear theorems and LISW Question 1.11 [IC].

**Not yet in the configuration**, because their statements need vocabulary Mathlib lacks
(finiteness properties `F_n`, Thompson-like groups, decision problems over `CT(ℤ)`):
Belk–Zaremsky Conjecture H and the FFWZ §1.2 conjecture, Kourovka 21.73 and 21.74(b),(c), Zaremsky's
Oberwolfach 2018 Question 110, Tarocchi's and Lodha's questions, and the remaining rows of the
summary; also the exceptional spherical Artin groups.

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

/-- The reflection `n ↦ -n - 1` of `ℤ`, which exchanges the nonnegative and the negative
integers. -/
def integerReflection : Equiv.Perm ℤ where
  toFun n := -n - 1
  invFun n := -n - 1
  left_inv n := show -(-n - 1) - 1 = n by omega
  right_inv n := show -(-n - 1) - 1 = n by omega

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

/-- An action of type (A) of `Γ` (Zaremsky; Belk–Fournier-Facio–Hyde–Zaremsky, §1): a
faithful action on a set `S` such that `Γ` is finitely presented, every point stabilizer is
finitely generated, and `Γ` has finitely many orbits on `S × S`. -/
def HasTypeAAction (Γ : Type) [Group Γ] : Prop :=
  ∃ (S : Type) (_ : MulAction Γ S), FaithfulSMul Γ S ∧ Group.IsFinitelyPresented Γ ∧
    (∀ s : S, (MulAction.stabilizer Γ s).FG) ∧
    Finite (MulAction.orbitRel.Quotient Γ (S × S))

/-- `G` satisfies the permutational Boone–Higman property: it embeds in a group admitting an
action of type (A). -/
def EmbedsInTypeAGroup (G : Type) [Group G] : Prop :=
  ∃ (Γ : Type) (_ : Group Γ), HasTypeAAction Γ ∧ ∃ f : G →* Γ, Function.Injective f

/-- The relators of a graph product: the commutators of elements of adjacent vertex groups. -/
def graphProductRelators {ι : Type} (Γ : SimpleGraph ι) (G : ι → Type) [∀ i, Group (G i)] :
    Set (Monoid.CoprodI G) :=
  {w | ∃ i j, Γ.Adj i j ∧ ∃ (a : G i) (b : G j),
    w = ⁅Monoid.CoprodI.of (M := G) a, Monoid.CoprodI.of (M := G) b⁆}

/-- The graph product of the groups `G i` over the simple graph `Γ`: their free product,
with `G i` and `G j` made to commute whenever `i` and `j` are adjacent. -/
abbrev GraphProduct {ι : Type} (Γ : SimpleGraph ι) (G : ι → Type) [∀ i, Group (G i)] :
    Type :=
  Monoid.CoprodI G ⧸ Subgroup.normalClosure (graphProductRelators Γ G)

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

/-- **Kourovka 14.10(c), BBMZ Problem 2.7**, proved outright:
`GroupApproximation.SteinbergFP.explicit_fp_overgroup_of_all_gl_n_q` states the same
proposition over byte-identical copies of the shared definitions, so it closes this one by
definitional unfolding. -/
theorem explicit_fp_overgroup_of_all_gl_n_q :
    Group.IsFinitelyPresented (SteinbergGroup 10 LeavittResolventRing) ∧
      ∀ n : ℕ, ∃ f : Matrix.GeneralLinearGroup (Fin n) ℚ →*
        SteinbergGroup 10 LeavittResolventRing, Function.Injective f :=
  GroupApproximation.SteinbergFP.explicit_fp_overgroup_of_all_gl_n_q

/-- The same statement under its `_of` name; no hypothesis is outstanding. -/
theorem explicit_fp_overgroup_of_all_gl_n_q_of :
    Group.IsFinitelyPresented (SteinbergGroup 10 LeavittResolventRing) ∧
      ∀ n : ℕ, ∃ f : Matrix.GeneralLinearGroup (Fin n) ℚ →*
        SteinbergGroup 10 LeavittResolventRing, Function.Injective f :=
  explicit_fp_overgroup_of_all_gl_n_q

/-- The four open inputs of route A, named Statements of the metabelian chain that
`GroupApproximation/BooneHigmanLinear/FrontierFour.lean` composes: `S1`, Suslin absorption in the
bad-prime local case; `P1`, the characteristic-`p` `K₂` gap pair; `Z1`, the characteristic-zero
`K₂` split gap; and `H1`, the step-B core of the Higman–`V` envelope. -/
def RouteAOwed : Prop :=
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZLocal_BadStatement ∧
    (∀ p : ℕ, p.Prime →
      GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2NilGapStatementOver (ZMod p) 4) ∧
    GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CharZeroK2SplitGapStatement ∧
    GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCStepBCoreStatement

/-- BBMZ Problem 5.3(7), from route A's four inputs, through
`GroupApproximation.BooneHigmanLinear.finitelyPresentedMetabelianStatement_routeA`. -/
theorem finitely_presented_metabelian_embeds_in_finitely_presented_simple_of
    (h : RouteAOwed) :
    ∀ (G : Type) [Group G], Group.IsFinitelyPresented G → IsMetabelianGroup G →
      EmbedsInFinitelyPresentedSimpleGroup G := by
  obtain ⟨hS1, hP1, hZ1, hH1⟩ := h
  intro G _ hfp hmet
  exact embedsInFinitelyPresentedSimpleGroup_iff.mpr
    (GroupApproximation.BooneHigmanLinear.finitelyPresentedMetabelianStatement_routeA
      hS1 hP1 hZ1 hH1 G hfp (isMetabelianGroup_iff.mp hmet))

/-- The finitely generated form of BBMZ Problem 5.3(7), from route A's four inputs, through
`GroupApproximation.BooneHigmanLinear.finitelyGeneratedMetabelianStatement_routeA`. -/
theorem finitely_generated_metabelian_embeds_in_finitely_presented_simple_of
    (h : RouteAOwed) :
    ∀ (G : Type) [Group G], Group.FG G → IsMetabelianGroup G →
      EmbedsInFinitelyPresentedSimpleGroup G := by
  obtain ⟨hS1, hP1, hZ1, hH1⟩ := h
  intro G _ hfg hmet
  exact embedsInFinitelyPresentedSimpleGroup_iff.mpr
    (GroupApproximation.BooneHigmanLinear.finitelyGeneratedMetabelianStatement_routeA
      hS1 hP1 hZ1 hH1 G hfg (isMetabelianGroup_iff.mp hmet))

/-- Finitely generated linear groups over any field, from route A's four inputs, through
`GroupApproximation.BooneHigmanLinear.finitelyGeneratedLinearStatement_routeA`. -/
theorem finitely_generated_linear_embeds_in_finitely_presented_simple_of
    (h : RouteAOwed) :
    ∀ (K : Type) [Field K] (n : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)),
      H.FG →
      EmbedsInFinitelyPresentedSimpleGroup H := by
  obtain ⟨hS1, hP1, hZ1, hH1⟩ := h
  intro K _ n H hfg
  exact embedsInFinitelyPresentedSimpleGroup_iff.mpr
    (GroupApproximation.BooneHigmanLinear.finitelyGeneratedLinearStatement_routeA
      hS1 hP1 hZ1 hH1 K n H hfg)

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

/-- The proposition the class-transposition development owes for Kourovka 17.57. -/
def Kourovka1757Owed : Prop :=
  (∀ g ∈ classTranspositionGroup,
    integerReflection * g * integerReflection⁻¹ ∈ classTranspositionGroup) ∧
  (∀ φ : MulAut classTranspositionGroup, ∃ h : Equiv.Perm ℤ,
    (h ∈ classTranspositionGroup ∨ integerReflection⁻¹ * h ∈ classTranspositionGroup) ∧
    ∀ x : classTranspositionGroup,
      ((φ x : classTranspositionGroup) : Equiv.Perm ℤ) = h * (x : Equiv.Perm ℤ) * h⁻¹) ∧
  ¬ ∃ h ∈ classTranspositionGroup, ∀ x ∈ classTranspositionGroup,
    integerReflection * x * integerReflection⁻¹ = h * x * h⁻¹

/-- Kourovka 17.57, from the proposition the class-transposition development owes. -/
theorem kourovka_17_57_of (h : Kourovka1757Owed) :
    (∀ g ∈ classTranspositionGroup,
      integerReflection * g * integerReflection⁻¹ ∈ classTranspositionGroup) ∧
    (∀ φ : MulAut classTranspositionGroup, ∃ h : Equiv.Perm ℤ,
      (h ∈ classTranspositionGroup ∨ integerReflection⁻¹ * h ∈ classTranspositionGroup) ∧
      ∀ x : classTranspositionGroup,
        ((φ x : classTranspositionGroup) : Equiv.Perm ℤ) = h * (x : Equiv.Perm ℤ) * h⁻¹) ∧
    ¬ ∃ h ∈ classTranspositionGroup, ∀ x ∈ classTranspositionGroup,
      integerReflection * x * integerReflection⁻¹ = h * x * h⁻¹ :=
  h

/-- The proposition the class-transposition development owes for Kourovka 17.59. -/
def Kourovka1759Owed : Prop :=
  (classTranspositionGroup : Set (Equiv.Perm ℤ)) =
    {g | IsResidueClassWiseAffine g ∧ ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n}

/-- Kourovka 17.59, from the proposition the class-transposition development owes. -/
theorem kourovka_17_59_of (h : Kourovka1759Owed) :
    (classTranspositionGroup : Set (Equiv.Perm ℤ)) =
      {g | IsResidueClassWiseAffine g ∧ ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n} :=
  h

/-- The proposition the class-transposition development owes for Kourovka 17.60. -/
def Kourovka1760Owed : Prop :=
  ∀ P Q : Set ℕ, (∀ p ∈ P, p.Prime ∧ p ≠ 2) → (∀ p ∈ Q, p.Prime ∧ p ≠ 2) →
    Nonempty (classTranspositionGroupOver P ≃* classTranspositionGroupOver Q) → P = Q

/-- Kourovka 17.60, from the proposition the class-transposition development owes. -/
theorem kourovka_17_60_of (h : Kourovka1760Owed) :
    ∀ P Q : Set ℕ, (∀ p ∈ P, p.Prime ∧ p ≠ 2) → (∀ p ∈ Q, p.Prime ∧ p ≠ 2) →
      Nonempty (classTranspositionGroupOver P ≃* classTranspositionGroupOver Q) → P = Q :=
  h

/-- The proposition the class-transposition development owes for Kourovka 17.61. -/
def Kourovka1761Owed : Prop :=
  ∀ P : Set ℕ, P.Finite → (∀ p ∈ P, p.Prime ∧ p ≠ 2) →
    Group.IsFinitelyPresented (classTranspositionGroupOver P)

/-- Kourovka 17.61, from the proposition the class-transposition development owes. -/
theorem kourovka_17_61_of (h : Kourovka1761Owed) :
    ∀ P : Set ℕ, P.Finite → (∀ p ∈ P, p.Prime ∧ p ≠ 2) →
      Group.IsFinitelyPresented (classTranspositionGroupOver P) :=
  h

/-- The proposition the class-transposition development owes for Kourovka 21.75. -/
def Kourovka2175Owed : Prop :=
  ∀ P₁ P₂ : Set ℕ, (∀ p ∈ P₁, p.Prime ∧ p ≠ 2) → (∀ p ∈ P₂, p.Prime ∧ p ≠ 2) →
    classTranspositionGroupOver P₁ ⊔ classTranspositionGroupOver P₂ =
      classTranspositionGroupOver (P₁ ∪ P₂)

/-- Kourovka 21.75, answered negatively, from the proposition the class-transposition
development owes. -/
theorem kourovka_21_75_of (h : Kourovka2175Owed) :
    ∀ P₁ P₂ : Set ℕ, (∀ p ∈ P₁, p.Prime ∧ p ≠ 2) → (∀ p ∈ P₂, p.Prime ∧ p ≠ 2) →
      classTranspositionGroupOver P₁ ⊔ classTranspositionGroupOver P₂ =
        classTranspositionGroupOver (P₁ ∪ P₂) :=
  h

/-- The proposition the class-transposition development owes for Kohl's factorization
conjecture. -/
def KohlFactorizationOwed : Prop :=
  {g : Equiv.Perm ℤ | IsResidueClassWiseAffine g} =
    (Subgroup.closure {g | IsClassShift g ∨ IsClassReflection g ∨ IsClassTransposition g} :
      Set (Equiv.Perm ℤ))

/-- Kohl's factorization conjecture, from the proposition the class-transposition
development owes. -/
theorem kohl_factorization_conjecture_of (h : KohlFactorizationOwed) :
    {g : Equiv.Perm ℤ | IsResidueClassWiseAffine g} =
      (Subgroup.closure {g | IsClassShift g ∨ IsClassReflection g ∨ IsClassTransposition g} :
        Set (Equiv.Perm ℤ)) :=
  h

/-- The proposition the graph-product development owes for BFFHZ Question 3.1. -/
def GraphProductOwed : Prop :=
  ∀ (ι : Type) [Finite ι] (Γ : SimpleGraph ι) (G : ι → Type) [∀ i, Group (G i)],
    (∀ i, EmbedsInTypeAGroup (G i)) → EmbedsInTypeAGroup (GraphProduct Γ G)

/-- BFFHZ Question 3.1, answered positively, from the proposition the graph-product
development owes. -/
theorem graph_product_embeds_in_type_a_group_of (h : GraphProductOwed) :
    ∀ (ι : Type) [Finite ι] (Γ : SimpleGraph ι) (G : ι → Type) [∀ i, Group (G i)],
      (∀ i, EmbedsInTypeAGroup (G i)) → EmbedsInTypeAGroup (GraphProduct Γ G) :=
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
