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
import Mathlib.Tactic.Linarith
import GroupApproximation.Sofic.Sofic
import GroupApproximation.Sofic.SoficAction
import GroupApproximation.CommutingSoficActions.Endpoint

/-!
# Proof of the GKP Question 4.2 theorems

This file repeats the challenge's shared block byte for byte, translates the
development's vocabulary into it, and proves the two theorems
`Palomar/comparator-gkp-commuting-actions.json` selects.

* `isSoficAction_of_repo` and `repo_of_isSoficAction`: for an action given by a
  `MulAction` instance, the challenge's `IsSoficAction` is the development's
  `GroupApproximation.IsSoficAction`.  The development's model at tolerance
  `ε / 2` is a GKP model at tolerance `ε`; conversely a GKP chart `π_s : E → B`
  extends to `X → Option B` by a fresh point off `E`.
* `isSoficGroup_of_isSofic`: the development's `GroupApproximation.IsSofic`
  gives the challenge's `IsSoficGroup`, after redefining the model at `1` so
  that it is unital.
* `isSoficAction_of_mulEquiv`: soficity of an action transfers along a group
  isomorphism compatible with the two actions.
* Model tests: a finite group acting on itself by left multiplication is a sofic
  action and a sofic group, and the one-point map is not an orbit approximation
  of `Sym(2)` acting on two points.
* `exists_commuting_sofic_actions_not_sofic_of` and
  `commuting_sofic_actions_need_not_combine_of` carry the development's
  counterexample into the challenge's two statements, the second over the
  index set `Bool`.

The counterexample is supplied by
`GroupApproximation.CommutingSoficActions.exists_commuting_sofic_actions_not_sofic`
in `GroupApproximation/CommutingSoficActions/Endpoint.lean`.

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

/-! ### Bridges from the development's vocabulary -/

/-- A sofic action in the development's sense is sofic in GKP's sense, for any
homomorphism `α` computing the action.  The development's model at tolerance
`ε / 2` is a GKP model at tolerance `ε`, with `π_s` the chart restricted to `E`. -/
theorem isSoficAction_of_repo {G X : Type} [Group G] [MulAction G X] (α : G →* Equiv.Perm X)
    (hα : ∀ g x, α g x = g • x) (h : GroupApproximation.IsSoficAction G X) :
    IsSoficAction α := by
  intro F E ε hε
  obtain ⟨m⟩ := h F E (ε / 2) (half_pos hε)
  refine ⟨⟨m.Site, m.siteFintype, m.siteDecEq⟩, m.act, m.act_one,
    fun g hg k hk ↦ lt_of_le_of_lt (m.act_mul g hg k hk) (half_lt_self hε),
    m.Chart, inferInstance, m.good, fun s x ↦ m.chart s x.1, ?_, ?_, ?_⟩
  · have hn : (0 : ℝ) < Fintype.card m.Site := by exact_mod_cast m.siteNonempty
    have hgood := m.good_card
    have hpos := mul_pos hε hn
    show (1 - ε) * (Fintype.card m.Site : ℝ) < (m.good.card : ℝ)
    linarith
  · intro s hs x y hxy
    exact Subtype.ext (m.chart_inj s hs x.1 x.2 y.1 y.2 hxy)
  · intro s hs g hg x hx hgs hgx
    have hgx' : g⁻¹ • x ∈ E := by rw [← hα]; exact hgx
    show m.chart (m.act g s) x = m.chart s (α g⁻¹ x)
    rw [hα]
    exact m.chart_equivariant g hg s hs hgs x hx hgx'

/-- A sofic action in GKP's sense is sofic in the development's sense.  The
development's chart is GKP's `π_s` on `E`, sending points off `E` to `none`. -/
theorem repo_of_isSoficAction {G X : Type} [Group G] [MulAction G X] (α : G →* Equiv.Perm X)
    (hα : ∀ g x, α g x = g • x) (h : IsSoficAction α) :
    GroupApproximation.IsSoficAction G X := by
  classical
  intro F E ε hε
  obtain ⟨A, φ, hunit, hmul, B, hB, S, π, hcard, hinj, hequiv⟩ := h F E ε hε
  haveI : Fintype B := Fintype.ofFinite B
  have hpos : 0 < Fintype.card A := by
    rcases Nat.eq_zero_or_pos (Fintype.card A) with h0 | h0
    · have hS : S.card = 0 := by
        have := Finset.card_le_univ S
        omega
      rw [h0, hS] at hcard
      simp at hcard
    · exact h0
  refine ⟨{
    Site := A
    siteFintype := A.fintype
    siteDecEq := A.decidableEq
    siteNonempty := hpos
    act := φ
    act_one := hunit
    act_mul := fun g hg k hk ↦ (hmul g hg k hk).le
    good := S
    good_card := hcard.le
    Chart := Option B
    chartFintype := inferInstance
    chart := fun s x ↦ if hx : x ∈ E then some (π s ⟨x, hx⟩) else none
    chart_inj := ?_
    chart_equivariant := ?_ }⟩
  · intro s hs x hx y hy hxy
    simp only [dif_pos hx, dif_pos hy, Option.some.injEq] at hxy
    exact congrArg Subtype.val (hinj s hs hxy)
  · intro g hg s hs hgs x hx hgx
    have hgx' : α g⁻¹ x ∈ E := by rw [hα]; exact hgx
    have key := hequiv s hs g hg x hx hgs hgx'
    have hsub : (⟨α g⁻¹ x, hgx'⟩ : E) = ⟨g⁻¹ • x, hgx⟩ := Subtype.ext (hα g⁻¹ x)
    simp only [dif_pos hx, dif_pos hgx]
    exact congrArg some (key.trans (congrArg (π s) hsub))

/-- A sofic group in the development's sense is sofic in GKP's sense.  The
development's model for `insert 1 F` at tolerance `ε / 5`, redefined to be `1`
at `1`, is a GKP model at tolerance `ε`. -/
theorem isSoficGroup_of_isSofic {G : Type} [Group G] (h : GroupApproximation.IsSofic G) :
    IsSoficGroup G := by
  classical
  intro F ε hε
  obtain ⟨m⟩ := h (insert 1 F) (ε / 5) (by linarith)
  obtain ⟨φ, hφ1, hφg⟩ :
      ∃ φ : G → Equiv.Perm m.carrier, φ 1 = 1 ∧ ∀ g, g ≠ 1 → φ g = m.map g :=
    ⟨fun g ↦ if g = 1 then 1 else m.map g, if_pos rfl, fun g hg ↦ if_neg hg⟩
  have h1F : (1 : G) ∈ insert 1 F := Finset.mem_insert_self 1 F
  have hone : GroupApproximation.hammingDistance m.carrier 1 (m.map 1) ≤ ε / 5 := by
    have h11 := m.multiplicative 1 h1F 1 h1F
    rw [mul_one] at h11
    rw [← GroupApproximation.hammingDistance_left_invariant m.carrier (m.map 1) 1 (m.map 1),
      mul_one]
    exact h11
  have hclose : ∀ g, GroupApproximation.hammingDistance m.carrier (φ g) (m.map g) ≤ ε / 5 := by
    intro g
    by_cases hg : g = 1
    · subst hg
      rw [hφ1]
      exact hone
    · rw [hφg g hg, GroupApproximation.hammingDistance_self]
      linarith
  refine ⟨⟨m.carrier.carrier, m.carrier.fintype, m.carrier.decidableEq⟩, φ, hφ1, ?_, ?_⟩
  · intro g hg k hk
    have hm := m.multiplicative g (Finset.mem_insert_of_mem hg) k (Finset.mem_insert_of_mem hk)
    have e0 := hclose (g * k)
    have e1 := hclose g
    have e2 := hclose k
    have i1 := GroupApproximation.hammingDistance_right_invariant m.carrier
      (m.map g) (φ g) (m.map k)
    have i2 := GroupApproximation.hammingDistance_left_invariant m.carrier
      (φ g) (m.map k) (φ k)
    have c1 := GroupApproximation.hammingDistance_comm m.carrier (m.map g) (φ g)
    have c2 := GroupApproximation.hammingDistance_comm m.carrier (m.map k) (φ k)
    have t1 := GroupApproximation.hammingDistance_triangle m.carrier
      (φ (g * k)) (m.map (g * k)) (m.map g * m.map k)
    have t2 := GroupApproximation.hammingDistance_triangle m.carrier
      (m.map g * m.map k) (φ g * m.map k) (φ g * φ k)
    have t3 := GroupApproximation.hammingDistance_triangle m.carrier
      (φ (g * k)) (m.map g * m.map k) (φ g * φ k)
    show GroupApproximation.hammingDistance m.carrier (φ (g * k)) (φ g * φ k) < ε
    linarith
  · intro g hg hg1
    have hs := m.separated 1 h1F g (Finset.mem_insert_of_mem hg) (Ne.symm hg1)
    have t := GroupApproximation.hammingDistance_triangle m.carrier (m.map 1) 1 (m.map g)
    have c := GroupApproximation.hammingDistance_comm m.carrier (m.map 1) 1
    show 1 - ε < GroupApproximation.hammingDistance m.carrier 1 (φ g)
    rw [hφg g hg1]
    linarith

/-- Soficity of an action transfers along a group isomorphism `e : K ≃* H`
compatible with the two actions. -/
theorem isSoficAction_of_mulEquiv {K H X : Type} [Group K] [Group H]
    (β : K →* Equiv.Perm X) (γ : H →* Equiv.Perm X) (e : K ≃* H)
    (hγβ : ∀ k, γ (e k) = β k) (h : IsSoficAction β) : IsSoficAction γ := by
  classical
  intro F E ε hε
  obtain ⟨A, φ, hunit, hmul, B, hB, S, π, hcard, hinj, hequiv⟩ := h (F.image e.symm) E ε hε
  refine ⟨A, fun g ↦ φ (e.symm g), ?_, ?_, B, hB, S, π, hcard, hinj, ?_⟩
  · show φ (e.symm 1) = 1
    rw [map_one]
    exact hunit
  · intro g hg k hk
    show hammingDist A (φ (e.symm (g * k))) (φ (e.symm g) * φ (e.symm k)) < ε
    rw [map_mul]
    exact hmul (e.symm g) (Finset.mem_image_of_mem _ hg) (e.symm k)
      (Finset.mem_image_of_mem _ hk)
  · intro s hs g hg x hx hgs hgx
    have hγ : γ g⁻¹ = β (e.symm g)⁻¹ := by
      rw [← map_inv e.symm, ← hγβ, MulEquiv.apply_symm_apply]
    have hgx' : β (e.symm g)⁻¹ x ∈ E := by rw [← hγ]; exact hgx
    have key := hequiv s hs (e.symm g) (Finset.mem_image_of_mem _ hg) x hx hgs hgx'
    have hsub : (⟨β (e.symm g)⁻¹ x, hgx'⟩ : E) = ⟨γ g⁻¹ x, hgx⟩ :=
      Subtype.ext (show β (e.symm g)⁻¹ x = γ g⁻¹ x by rw [hγ])
    exact key.trans (congrArg (π s) hsub)

/-! ### Model tests -/

/-- Model test: a finite group acting on itself by left multiplication is a sofic
action, witnessed by the action itself with the charts `x ↦ s⁻¹ x`. -/
theorem isSoficAction_toPermHom_self (G : Type) [Group G] [Fintype G] [DecidableEq G] :
    IsSoficAction (MulAction.toPermHom G G) := by
  intro F E ε hε
  refine ⟨⟨G, inferInstance, inferInstance⟩, MulAction.toPermHom G G, map_one _, ?_,
    G, inferInstance, Finset.univ, (fun (s : G) (x : E) ↦ s⁻¹ * (x : G)), ?_, ?_, ?_⟩
  · intro g _ k _
    rw [map_mul]
    simpa [hammingDist] using hε
  · have hn : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨1⟩
    have hpos := mul_pos hε hn
    show (1 - ε) * (Fintype.card G : ℝ) < ((Finset.univ : Finset G).card : ℝ)
    rw [Finset.card_univ]
    linarith
  · intro s _ x y hxy
    exact Subtype.ext (mul_left_cancel hxy)
  · intro s _ g _ x hx _ hgx
    simp [mul_assoc]

/-- Model test: a finite group is sofic, witnessed by its left regular
representation, which moves every point when `g ≠ 1`. -/
theorem isSoficGroup_of_finite (G : Type) [Group G] [Fintype G] [DecidableEq G] :
    IsSoficGroup G := by
  intro F ε hε
  refine ⟨⟨G, inferInstance, inferInstance⟩, MulAction.toPermHom G G, map_one _, ?_, ?_⟩
  · intro g _ k _
    rw [map_mul]
    simpa [hammingDist] using hε
  · intro g _ hg1
    have hn : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hall : (Finset.univ.filter fun a : G ↦
        (1 : Equiv.Perm G) a ≠ MulAction.toPermHom G G g a) = Finset.univ := by
      refine Finset.filter_true_of_mem fun a _ ↦ ?_
      simpa using hg1
    show 1 - ε < ((Finset.univ.filter fun a : G ↦
      (1 : Equiv.Perm G) a ≠ MulAction.toPermHom G G g a).card : ℝ) / Fintype.card G
    rw [hall, Finset.card_univ, div_self hn]
    linarith

/-- Model test, negative: the one-point map is not an orbit approximation of
`Sym(2)` acting on two points at any tolerance `ε < 1`.  Some model point is good,
and its chart would have to identify the two points swapped by `Equiv.swap 0 1`. -/
theorem not_isOrbitApproximation_onePoint (ε : ℝ) (hε : ε < 1) :
    ¬ IsOrbitApproximation (MonoidHom.id (Equiv.Perm (Fin 2)))
      (A := ⟨Unit, inferInstance, inferInstance⟩) (fun _ ↦ 1) {Equiv.swap 0 1}
      Finset.univ ε := by
  rintro ⟨B, _, S, π, hcard, hinj, hequiv⟩
  have hS : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h0 | h0
    · rw [h0, Finset.card_empty, Nat.cast_zero] at hcard
      exact absurd hcard (not_lt.mpr (mul_nonneg (by linarith) (Nat.cast_nonneg _)))
    · exact h0
  obtain ⟨s, hs⟩ := hS
  have key := hequiv s hs (Equiv.swap 0 1) (Finset.mem_singleton_self _) 0
    (Finset.mem_univ _) hs (Finset.mem_univ _)
  have hv : (0 : Fin 2) = (MonoidHom.id (Equiv.Perm (Fin 2))) (Equiv.swap 0 1)⁻¹ 0 :=
    congrArg Subtype.val (hinj s hs key)
  have h10 : (MonoidHom.id (Equiv.Perm (Fin 2))) (Equiv.swap 0 1)⁻¹ (0 : Fin 2) = 1 := by
    simp [Equiv.swap_inv]
  rw [h10] at hv
  exact absurd hv (by decide)

/-- Model test, negative: a one-point model never separates `g ≠ 1` from `1`, so
the separation clause of `IsSoficGroup` is not vacuous. -/
theorem onePoint_not_separated {G : Type} [Group G] (φ : G → Equiv.Perm Unit) (g : G) :
    ¬ 0 < hammingDist ⟨Unit, inferInstance, inferInstance⟩ 1 (φ g) := by
  have hempty : (Finset.univ.filter fun a : Unit ↦ (1 : Equiv.Perm Unit) a ≠ φ g a) = ∅ :=
    Finset.filter_false_of_mem fun a _ ↦ not_not.mpr (Subsingleton.elim _ _)
  show ¬ 0 < ((Finset.univ.filter fun a : Unit ↦
    (1 : Equiv.Perm Unit) a ≠ φ g a).card : ℝ) / Fintype.card Unit
  rw [hempty, Finset.card_empty, Nat.cast_zero, zero_div]
  exact lt_irrefl 0

/-! ### The two theorems -/

/-- The development's counterexample gives two commuting sofic actions of a
sofic group whose combined action is not sofic: the coordinate actions
`g ↦ (g, 1)` and `h ↦ (1, h)` of an action of `G × G`. -/
theorem exists_commuting_sofic_actions_not_sofic_of
    (hend : ∃ (G X : Type) (_ : Group G) (_ : MulAction (G × G) X),
      Countable G ∧ Countable X ∧ GroupApproximation.IsSofic G ∧
        @GroupApproximation.IsSoficAction G _ X (MulAction.compHom X (MonoidHom.inl G G)) ∧
        @GroupApproximation.IsSoficAction G _ X (MulAction.compHom X (MonoidHom.inr G G)) ∧
        ¬ GroupApproximation.IsSoficAction (G × G) X) :
    ∃ (G X : Type) (_ : Group G) (_ : Countable G) (_ : Countable X)
      (α₁ α₂ : G →* Equiv.Perm X) (hcomm : ∀ (g h : G), Commute (α₁ g) (α₂ h)),
      IsSoficGroup G ∧ IsSoficAction α₁ ∧ IsSoficAction α₂ ∧
        ¬ IsSoficAction (combinedActionPair α₁ α₂ hcomm) := by
  obtain ⟨G, X, _, _, hG, hX, hsofic, h₁, h₂, hnot⟩ := hend
  refine ⟨G, X, inferInstance, hG, hX,
    (MulAction.toPermHom (G × G) X).comp (MonoidHom.inl G G),
    (MulAction.toPermHom (G × G) X).comp (MonoidHom.inr G G),
    fun g h ↦ (MonoidHom.commute_inl_inr g h).map (MulAction.toPermHom (G × G) X),
    isSoficGroup_of_isSofic hsofic,
    @isSoficAction_of_repo G X _ (MulAction.compHom X (MonoidHom.inl G G))
      ((MulAction.toPermHom (G × G) X).comp (MonoidHom.inl G G)) (fun _ _ ↦ rfl) h₁,
    @isSoficAction_of_repo G X _ (MulAction.compHom X (MonoidHom.inr G G))
      ((MulAction.toPermHom (G × G) X).comp (MonoidHom.inr G G)) (fun _ _ ↦ rfl) h₂,
    fun hc ↦ hnot (repo_of_isSoficAction _ ?_ hc)⟩
  rintro ⟨g, h⟩ x
  show ((g, 1) : G × G) • (((1, h) : G × G) • x) = (g, h) • x
  rw [smul_smul, Prod.mk_mul_mk, mul_one, one_mul]

/-- Two commuting sofic actions whose combined action is not sofic refute the
biconditional of Question 4.2 over the index set `Bool`. -/
theorem commuting_sofic_actions_need_not_combine_of
    (hex : ∃ (G X : Type) (_ : Group G) (_ : Countable G) (_ : Countable X)
      (α₁ α₂ : G →* Equiv.Perm X) (hcomm : ∀ (g h : G), Commute (α₁ g) (α₂ h)),
      IsSoficGroup G ∧ IsSoficAction α₁ ∧ IsSoficAction α₂ ∧
        ¬ IsSoficAction (combinedActionPair α₁ α₂ hcomm)) :
    ¬ ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Countable (G i)]
      (X : Type) [Countable X] (α : ∀ i, G i →* Equiv.Perm X) (hcomm : ActionsCommute α),
      (IsSoficAction (combinedAction α hcomm) ↔ ∀ i, IsSoficAction (α i)) := by
  obtain ⟨G, X, _, hG, hX, α₁, α₂, hcomm, -, h₁, h₂, hnot⟩ := hex
  intro hall
  obtain ⟨α, hαt, hαf⟩ : ∃ α : Bool → (G →* Equiv.Perm X), α true = α₁ ∧ α false = α₂ :=
    ⟨fun b ↦ Bool.rec α₂ α₁ b, rfl, rfl⟩
  have hcommα : ActionsCommute (G := fun _ : Bool ↦ G) α := by
    intro i j hij g h
    cases i <;> cases j
    · exact absurd rfl hij
    · rw [hαf, hαt]
      exact (hcomm h g).symm
    · rw [hαt, hαf]
      exact hcomm g h
    · exact absurd rfl hij
  have hiff := hall Bool (fun _ ↦ G) X α hcommα
  let e : (∀ _ : Bool, G) ≃* G × G :=
    { toFun := fun f ↦ (f true, f false)
      invFun := fun p b ↦ cond b p.1 p.2
      left_inv := fun f ↦ by funext b; cases b <;> rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  have h1 : ∀ f : ∀ _ : Bool, G,
      combinedAction (G := fun _ : Bool ↦ G) α hcommα f = α₁ (f true) * α₂ (f false) := by
    intro f
    have hf : f = Pi.mulSingle true (f true) * Pi.mulSingle false (f false) := by
      funext b
      cases b <;> simp
    conv_lhs => rw [hf]
    simp only [combinedAction, map_mul, MonoidHom.noncommPiCoprod_mulSingle, hαt, hαf]
  apply hnot
  refine isSoficAction_of_mulEquiv (combinedAction (G := fun _ : Bool ↦ G) α hcommα) _ e
    ?_ (hiff.mpr ?_)
  · intro f
    refine Eq.trans ?_ (h1 f).symm
    rfl
  · intro i
    cases i
    · rw [hαf]
      exact h₂
    · rw [hαt]
      exact h₁

/-- **Two commuting sofic actions that do not combine**: some countable sofic
group `G` has two commuting sofic actions `α₁, α₂` on a countable set `X` whose
combined action `(g, h) ↦ α₁(g) α₂(h)` of `G × G` is not sofic. -/
theorem exists_commuting_sofic_actions_not_sofic :
    ∃ (G X : Type) (_ : Group G) (_ : Countable G) (_ : Countable X)
      (α₁ α₂ : G →* Equiv.Perm X) (hcomm : ∀ (g h : G), Commute (α₁ g) (α₂ h)),
      IsSoficGroup G ∧ IsSoficAction α₁ ∧ IsSoficAction α₂ ∧
        ¬ IsSoficAction (combinedActionPair α₁ α₂ hcomm) :=
  exists_commuting_sofic_actions_not_sofic_of
    GroupApproximation.CommutingSoficActions.exists_commuting_sofic_actions_not_sofic

/-- **Question 4.2 has a negative answer.**  For commuting actions `α_i` of
countable groups `G_i` on a countable set `X`, with `i` ranging over a finite
index set, it is not true in general that the combined action of
`⊕_i G_i = Π_i G_i` is sofic if and only if every `α_i` is sofic. -/
theorem commuting_sofic_actions_need_not_combine :
    ¬ ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Countable (G i)]
      (X : Type) [Countable X] (α : ∀ i, G i →* Equiv.Perm X) (hcomm : ActionsCommute α),
      (IsSoficAction (combinedAction α hcomm) ↔ ∀ i, IsSoficAction (α i)) :=
  commuting_sofic_actions_need_not_combine_of exists_commuting_sofic_actions_not_sofic

end

end GKPCommutingActions
