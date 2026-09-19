/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.Perm.Basic

/-!
# Gao–Kunnawalkam Elayavalli–Patchell Question 4.2: commuting sofic actions

D. Gao, S. Kunnawalkam Elayavalli and G. Patchell, *Soficity for group actions
on sets and applications* (arXiv:2401.04945v3; Res. Math. Sci. 12 (2025) 48),
ask as Question 4.2 (p. 14):

> Suppose we have actions α_i : G_i ↷ X which commute with each other and where
> i ranges over a countable index set. [...] α is sofic iff all α_i are sofic?

The elided sentence introduces `α` as the action of the direct sum `⊕_i G_i` on
`X` that the commuting actions give.  GKP note (p. 15) that the forward
direction follows from their Proposition 2.15(3), and that by Proposition
2.15(4) it suffices to consider two groups.  They also show that a positive
answer would give a positive answer to their Question 4.4, the converse of
their Theorem 3.6 on generalized wreath products.

The two theorems below answer **no**:

* `exists_commuting_sofic_actions_not_sofic` gives a countable sofic group `G`
  and two commuting sofic actions `α₁, α₂` of `G` on a countable set `X` whose
  combined action of `G × G` is not sofic;
* `commuting_sofic_actions_need_not_combine` negates the biconditional of
  Question 4.2 over finite index sets.

## Vocabulary

Every notion except the definitions in the shared block is Mathlib's.

* An action `α : G ↷ X` is a homomorphism `α : G →* Equiv.Perm X`, and `α g x`
  is the action of `g` on `x`.  `Sym(A)` is `Equiv.Perm A`.
* `FiniteCarrier` is a finite set `A` with its `Fintype` and `DecidableEq`
  structures, and `hammingDist A` is the normalized Hamming distance `d` on
  `Sym(A)`.
* `IsUnital`, `IsMultiplicative`, `IsOrbitApproximation`, `IsSoficGroup` and
  `IsSoficAction` are items (1)–(5) of GKP Definition 2.1 (p. 3).
* `ActionsCommute α` says that the actions `α_i` commute with each other.
  Over a finite index set the direct sum `⊕_i G_i` is the product `Π_i G_i`,
  and `combinedAction α hcomm` (Mathlib's `MonoidHom.noncommPiCoprod`) sends
  `(g_i)_i` to the product of the commuting permutations `α_i(g_i)`.  For two
  actions, `combinedActionPair α₁ α₂ hcomm` (Mathlib's
  `MonoidHom.noncommCoprod`) sends `(g, h)` to `α₁(g) α₂(h)`.
* GKP's standing assumptions make the groups and the set countable, so the
  theorems carry `Countable` hypotheses.  A counterexample over a finite index
  set is a counterexample over a countable one.

All groups and sets are quantified over `Type`, where the counterexample lives.

The prose of this module was written by Claude (Anthropic).
-/

namespace GKPCommutingActions

noncomputable section

-- BEGIN SHARED BLOCK (kept byte-identical in `Palomar/GKPCommutingActionsChallenge.lean` and `Palomar/GKPCommutingActionsSolution.lean`)

/-- A finite set `A`, bundled with the structure needed to count inside it. -/
structure FiniteCarrier where
  carrier : Type
  fintype : Fintype carrier
  decidableEq : DecidableEq carrier

instance finiteCarrierCoeSort : CoeSort FiniteCarrier Type :=
  ⟨FiniteCarrier.carrier⟩

@[reducible, instance] def finiteCarrierFintype (A : FiniteCarrier) :
    Fintype A :=
  A.fintype

@[reducible, instance] def finiteCarrierDecidableEq (A : FiniteCarrier) :
    DecidableEq A :=
  A.decidableEq

/-- The normalized Hamming distance `d` on `Sym(A)`: the proportion of points of
`A` where two permutations differ. -/
def hammingDist (A : FiniteCarrier) (p q : Equiv.Perm A) : ℝ :=
  ((Finset.univ.filter fun a : A ↦ p a ≠ q a).card : ℝ) / Fintype.card A

/-- GKP Definition 2.1(1), p. 3: a map `φ : G → Sym(A)` is *unital* if
`φ(1_G) = 1`. -/
def IsUnital {G : Type} [Group G] {A : FiniteCarrier} (φ : G → Equiv.Perm A) : Prop :=
  φ 1 = 1

/-- GKP Definition 2.1(2), p. 3: for a finite `F ⊆ G` and `ε > 0`, `φ` is
*`(F, ε)`-multiplicative* if `d(φ(gh), φ(g)φ(h)) < ε` for all `g, h ∈ F`. -/
def IsMultiplicative {G : Type} [Group G] {A : FiniteCarrier} (φ : G → Equiv.Perm A)
    (F : Finset G) (ε : ℝ) : Prop :=
  ∀ g ∈ F, ∀ h ∈ F, hammingDist A (φ (g * h)) (φ g * φ h) < ε

/-- GKP Definition 2.1(3), p. 3: for finite `F ⊆ G`, `E ⊆ X` and `ε > 0`, `φ` is
an *`(F, E, ε)`-orbit approximation* of `α` if there are a finite set `B`, a
subset `S ⊆ A` with `|S| > (1 - ε)|A|`, and for each `s ∈ S` an injective map
`π_s : E → B`, such that `π_{φ(g)s}(x) = π_s(α(g⁻¹)x)` for all `s ∈ S`, `g ∈ F`
and `x ∈ E` with `φ(g)s ∈ S` and `α(g⁻¹)x ∈ E`.  The maps `π_s` are given for
every `s ∈ A` and constrained only for `s ∈ S`. -/
def IsOrbitApproximation {G X : Type} [Group G] (α : G →* Equiv.Perm X)
    {A : FiniteCarrier} (φ : G → Equiv.Perm A) (F : Finset G) (E : Finset X) (ε : ℝ) :
    Prop :=
  ∃ (B : Type) (_ : Finite B) (S : Finset A) (π : A → E → B),
    (1 - ε) * (Fintype.card A : ℝ) < (S.card : ℝ) ∧
    (∀ s ∈ S, Function.Injective (π s)) ∧
    ∀ s ∈ S, ∀ g ∈ F, ∀ (x : X) (hx : x ∈ E), φ g s ∈ S → ∀ (hgx : α g⁻¹ x ∈ E),
      π (φ g s) ⟨x, hx⟩ = π s ⟨α g⁻¹ x, hgx⟩

/-- GKP Definition 2.1(4), p. 3: `G` is *sofic* if for all finite `F ⊆ G` and
`ε > 0` there are a finite set `A` and a unital, `(F, ε)`-multiplicative map
`φ : G → Sym(A)` with `d(1, φ(g)) > 1 - ε` for all `g ∈ F \ {e}`. -/
def IsSoficGroup (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (A : FiniteCarrier) (φ : G → Equiv.Perm A),
      IsUnital φ ∧ IsMultiplicative φ F ε ∧
        ∀ g ∈ F, g ≠ 1 → 1 - ε < hammingDist A 1 (φ g)

/-- GKP Definition 2.1(5), p. 3: an action `α : G ↷ X` is *sofic* if for all
finite `F ⊆ G`, `E ⊆ X` and `ε > 0` there are a finite set `A` and a map
`φ : G → Sym(A)` which is unital, `(F, ε)`-multiplicative and an
`(F, E, ε)`-orbit approximation of `α`. -/
def IsSoficAction {G X : Type} [Group G] (α : G →* Equiv.Perm X) : Prop :=
  ∀ (F : Finset G) (E : Finset X) (ε : ℝ), 0 < ε →
    ∃ (A : FiniteCarrier) (φ : G → Equiv.Perm A),
      IsUnital φ ∧ IsMultiplicative φ F ε ∧ IsOrbitApproximation α φ F E ε

/-- GKP Question 4.2, p. 14: actions `α_i : G_i ↷ X` *commute with each other* if
`α_i(g)` and `α_j(h)` commute for all `i ≠ j`, `g ∈ G_i` and `h ∈ G_j`. -/
def ActionsCommute {ι : Type} {G : ι → Type} [∀ i, Group (G i)] {X : Type}
    (α : ∀ i, G i →* Equiv.Perm X) : Prop :=
  Pairwise fun i j => ∀ (g : G i) (h : G j), Commute (α i g) (α j h)

/-- GKP Question 4.2, p. 14: commuting actions `α_i : G_i ↷ X` "naturally give
rise to an action α : ⊕i Gi ↷ X".  Over a finite index set `⊕_i G_i = Π_i G_i`,
and `α` sends `(g_i)_i` to the product of the commuting permutations `α_i(g_i)`. -/
def combinedAction {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] {X : Type}
    (α : ∀ i, G i →* Equiv.Perm X) (hcomm : ActionsCommute α) :
    (∀ i, G i) →* Equiv.Perm X :=
  MonoidHom.noncommPiCoprod α hcomm

/-- The case of two groups, to which GKP reduce Question 4.2 (p. 15): commuting
actions `α₁ : G₁ ↷ X` and `α₂ : G₂ ↷ X` give the action `(g, h) ↦ α₁(g) α₂(h)`
of `G₁ ⊕ G₂ = G₁ × G₂`. -/
def combinedActionPair {G₁ G₂ X : Type} [Group G₁] [Group G₂]
    (α₁ : G₁ →* Equiv.Perm X) (α₂ : G₂ →* Equiv.Perm X)
    (hcomm : ∀ (g : G₁) (h : G₂), Commute (α₁ g) (α₂ h)) : G₁ × G₂ →* Equiv.Perm X :=
  α₁.noncommCoprod α₂ hcomm

-- END SHARED BLOCK

/-- **Question 4.2 has a negative answer.**  For commuting actions `α_i` of
countable groups `G_i` on a countable set `X`, with `i` ranging over a finite
index set, it is not true in general that the combined action of
`⊕_i G_i = Π_i G_i` is sofic if and only if every `α_i` is sofic. -/
theorem commuting_sofic_actions_need_not_combine :
    ¬ ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Countable (G i)]
      (X : Type) [Countable X] (α : ∀ i, G i →* Equiv.Perm X) (hcomm : ActionsCommute α),
      (IsSoficAction (combinedAction α hcomm) ↔ ∀ i, IsSoficAction (α i)) := by
  sorry

/-- **Two commuting sofic actions that do not combine**: some countable sofic
group `G` has two commuting sofic actions `α₁, α₂` on a countable set `X` whose
combined action `(g, h) ↦ α₁(g) α₂(h)` of `G × G` is not sofic. -/
theorem exists_commuting_sofic_actions_not_sofic :
    ∃ (G X : Type) (_ : Group G) (_ : Countable G) (_ : Countable X)
      (α₁ α₂ : G →* Equiv.Perm X) (hcomm : ∀ (g h : G), Commute (α₁ g) (α₂ h)),
      IsSoficGroup G ∧ IsSoficAction α₁ ∧ IsSoficAction α₂ ∧
        ¬ IsSoficAction (combinedActionPair α₁ α₂ hcomm) := by
  sorry

end

end GKPCommutingActions
