/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Graph products and the permutational Boone–Higman class: definitions and statements

J. Belk, F. Fournier-Facio, J. Hyde and M. C. B. Zaremsky, *Finitely presented simple
groups and the Boone–Higman conjecture for Aut(F_n)*, arXiv:2503.21882v2 (BFFHZ):

> **Question 3.1.** Let `G` be a graph product over a finite graph such that each vertex
> group satisfies PBH. Does `G` satisfy PBH?

## Definitions (BFFHZ §1)

* A faithful action of a group `Γ` on a set `S` is of **type (A)** when `Γ` is finitely
  presented, every point stabilizer is finitely generated, and the diagonal action on
  `S × S` has finitely many orbits (`IsTypeA`).
* A group **satisfies PBH** when it embeds in a group admitting an action of type (A)
  (`SatisfiesPBH`). BFFHZ add that for a finitely generated group this implicitly includes a
  solvable word problem. That is a consequence of the embedding (Zaremsky), not an extra
  condition, so it is not part of the definition.
* The **graph product** of vertex groups `G v` over a simple graph `Γ` is the free product of
  the `G v` modulo the commutators `[a, b]` with `a ∈ G u`, `b ∈ G v` and `u, v` adjacent
  (`GraphProduct`).

## Statements

* `Question31`: BFFHZ Question 3.1 with a positive answer.
* `RetractAmalgamClosure`: the class is closed under `X *_C (C × K)` for a retract `C` of
  `X` (the key step; with `K = ℤ` it is the centralizing HNN extension).
* `relAut H n`: the group `Aut_H(H ∗ F_n)` of automorphisms fixing `H` pointwise, as in
  BFFHZ Theorem E.

Groups and sets live in `Type`. Actions are Mathlib's `MulAction` (left actions), finite
presentation is `Group.IsFinitelyPresented`, and faithfulness is `FaithfulSMul`.
-/

namespace GroupApproximation.BHPalomar.GraphProducts

open Monoid

-- BEGIN SHARED BLOCK

/-- An action of `Γ` on `S` of **type (A)** (BFFHZ §1): faithful, `Γ` finitely presented,
every point stabilizer finitely generated, and finitely many orbits on `S × S`. -/
def IsTypeA (Γ S : Type) [Group Γ] [MulAction Γ S] : Prop :=
  FaithfulSMul Γ S ∧ Group.IsFinitelyPresented Γ ∧ (∀ s : S, (MulAction.stabilizer Γ s).FG) ∧
    Finite (MulAction.orbitRel.Quotient Γ (S × S))

/-- `G` **satisfies PBH** (BFFHZ): it embeds in a group admitting an action of type (A). -/
def SatisfiesPBH (G : Type) [Group G] : Prop :=
  ∃ (Γ : Type) (_ : Group Γ) (S : Type) (_ : MulAction Γ S), IsTypeA Γ S ∧
    ∃ f : G →* Γ, Function.Injective f

/-- The defining relators of a graph product: commutators of elements of adjacent vertex
groups. -/
def graphProductRels {V : Type} (Γ : SimpleGraph V) (G : V → Type) [∀ v, Group (G v)] :
    Set (CoprodI G) :=
  {w | ∃ u v : V, Γ.Adj u v ∧ ∃ (a : G u) (b : G v),
    w = CoprodI.of a * CoprodI.of b * (CoprodI.of a)⁻¹ * (CoprodI.of b)⁻¹}

/-- The **graph product** of the vertex groups `G v` over the simple graph `Γ`. -/
abbrev GraphProduct {V : Type} (Γ : SimpleGraph V) (G : V → Type) [∀ v, Group (G v)] :
    Type :=
  CoprodI G ⧸ Subgroup.normalClosure (graphProductRels Γ G)

/-- **BFFHZ Question 3.1, positive answer**: a graph product over a finite simple graph of
groups satisfying PBH satisfies PBH. -/
def Question31 : Prop :=
  ∀ (V : Type) [Finite V] (Γ : SimpleGraph V) (G : V → Type) [∀ v, Group (G v)],
    (∀ v, SatisfiesPBH (G v)) → SatisfiesPBH (GraphProduct Γ G)

-- END SHARED BLOCK

/-- The relators of the amalgam `X *_C (C × K)`: `ι c` in `X` equals `(c, 1)` in `C × K`. -/
def retractAmalgamRels {X C : Type} [Group X] [Group C] (ι : C →* X) (K : Type) [Group K] :
    Set (Coprod X (C × K)) :=
  Set.range fun c : C => Coprod.inl (ι c) * (Coprod.inr (c, 1))⁻¹

/-- The amalgamated product `X *_C (C × K)` along `ι : C → X` and `c ↦ (c, 1)`. -/
abbrev RetractAmalgam {X C : Type} [Group X] [Group C] (ι : C →* X) (K : Type) [Group K] :
    Type :=
  Coprod X (C × K) ⧸ Subgroup.normalClosure (retractAmalgamRels ι K)

/-- Closure of the PBH class under amalgams `X *_C (C × K)` over a retract `C` of `X`. -/
def RetractAmalgamClosure : Prop :=
  ∀ (X C K : Type) [Group X] [Group C] [Group K] (ι : C →* X) (r : X →* C),
    (∀ c, r (ι c) = c) → SatisfiesPBH X → SatisfiesPBH K → SatisfiesPBH (RetractAmalgam ι K)

/-- `Aut_H(H ∗ F_n)`: automorphisms of `H ∗ F_n` fixing `H` pointwise (BFFHZ Theorem E). -/
def relAut (H : Type) [Group H] (n : ℕ) : Subgroup (MulAut (Coprod H (FreeGroup (Fin n)))) where
  carrier := {α | ∀ h : H, α (Coprod.inl h) = Coprod.inl h}
  mul_mem' := by
    intro a b ha hb
    show ∀ h : H, (a * b) (Coprod.inl h) = Coprod.inl h
    intro h
    rw [MulAut.mul_apply, hb h, ha h]
  one_mem' := by
    show ∀ h : H, (1 : MulAut (Coprod H (FreeGroup (Fin n)))) (Coprod.inl h) = Coprod.inl h
    intro h
    exact MulAut.one_apply _
  inv_mem' := by
    intro a ha
    show ∀ h : H, a⁻¹ (Coprod.inl h) = Coprod.inl h
    intro h
    conv_lhs => rw [← ha h]
    exact MulAut.inv_apply_self a _

theorem mem_relAut {H : Type} [Group H] {n : ℕ} {α : MulAut (Coprod H (FreeGroup (Fin n)))} :
    α ∈ relAut H n ↔ ∀ h : H, α (Coprod.inl h) = Coprod.inl h :=
  Iff.rfl

/-- Subgroups of groups satisfying PBH satisfy PBH. -/
theorem SatisfiesPBH.of_injective {G G' : Type} [Group G] [Group G'] (hG' : SatisfiesPBH G')
    (f : G →* G') (hf : Function.Injective f) : SatisfiesPBH G := by
  obtain ⟨Γ, _, S, _, hA, g, hg⟩ := hG'
  exact ⟨Γ, inferInstance, S, inferInstance, hA, g.comp f, hg.comp hf⟩

/-- A group admitting an action of type (A) satisfies PBH. -/
theorem SatisfiesPBH.of_isTypeA {Γ S : Type} [Group Γ] [MulAction Γ S] (h : IsTypeA Γ S) :
    SatisfiesPBH Γ :=
  ⟨Γ, inferInstance, S, inferInstance, h, MonoidHom.id Γ, Function.injective_id⟩

end GroupApproximation.BHPalomar.GraphProducts
