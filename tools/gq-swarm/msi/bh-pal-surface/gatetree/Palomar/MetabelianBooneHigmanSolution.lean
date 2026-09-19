/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Subgroup.Simple
import GroupApproximation.BooneHigman.Statement.API

/-!
# Proof of the theorems on the Boone–Higman conjecture for metabelian groups

This file repeats the challenge's shared block byte for byte and translates the
development's vocabulary into it.

**Status: skeleton.**  The development does not yet prove its endpoint
`GroupApproximation.BooneHigman.FinitelyGeneratedMetabelianStatement`, so each
theorem below takes it as a hypothesis, under a name ending `_of`.  The
unsuffixed theorems that `Palomar/comparator-metabelian-boone-higman.json`
selects are added, and the hypothesis removed, on the day the endpoint is proved.

* `isMetabelianGroup_iff` and `embedsInFinitelyPresentedSimpleGroup_iff`: the
  challenge's two definitions are the development's
  `GroupApproximation.BooneHigman.IsMetabelianGroup` and
  `GroupApproximation.BooneHigman.EmbedsInFinitelyPresentedSimpleGroup` at
  `Type`, with the same bodies.
* `finitely_generated_metabelian_embeds_in_finitely_presented_simple_of`: the
  finitely generated form, from the development endpoint.
* `finitely_presented_metabelian_embeds_in_finitely_presented_simple_of`: item
  (7) of Problem 5.3, from the same endpoint, because a finitely presented group
  is finitely generated
  (`GroupApproximation.BooneHigman.finitelyPresentedMetabelianStatement_of_finitelyGenerated`).

The prose of this module was written by Claude (Anthropic).
-/

namespace MetabelianBooneHigman

-- BEGIN SHARED BLOCK (kept byte-identical in `Palomar/MetabelianBooneHigmanChallenge.lean` and `Palomar/MetabelianBooneHigmanSolution.lean`)

/-- A group is metabelian when its derived subgroup `G' = ⁅G, G⁆` is abelian, that
is, when the second derived subgroup `⁅G', G'⁆` is trivial. -/
def IsMetabelianGroup (G : Type) [Group G] : Prop :=
  ⁅commutator G, commutator G⁆ = ⊥

/-- `G` embeds into some finitely presented simple group: the target of the
Boone–Higman conjecture (Belk–Bleak–Matucci–Zaremsky, arXiv:2306.16356v3,
page 1). -/
def EmbedsInFinitelyPresentedSimpleGroup (G : Type) [Group G] : Prop :=
  ∃ (S : Type) (_ : Group S), Group.IsFinitelyPresented S ∧ IsSimpleGroup S ∧
    ∃ f : G →* S, Function.Injective f

-- END SHARED BLOCK

/-- The challenge's metabelian groups are the development's. -/
theorem isMetabelianGroup_iff {G : Type} [Group G] :
    IsMetabelianGroup G ↔ GroupApproximation.BooneHigman.IsMetabelianGroup G :=
  Iff.rfl

/-- The challenge's embeddings in finitely presented simple groups are the
development's. -/
theorem embedsInFinitelyPresentedSimpleGroup_iff {G : Type} [Group G] :
    EmbedsInFinitelyPresentedSimpleGroup G ↔
      GroupApproximation.BooneHigman.EmbedsInFinitelyPresentedSimpleGroup G :=
  Iff.rfl

/-- The finitely generated form, from the development endpoint. -/
theorem finitely_generated_metabelian_embeds_in_finitely_presented_simple_of
    (h : GroupApproximation.BooneHigman.FinitelyGeneratedMetabelianStatement) :
    ∀ (G : Type) [Group G], Group.FG G → IsMetabelianGroup G →
      EmbedsInFinitelyPresentedSimpleGroup G := by
  intro G _ hfg hmet
  exact embedsInFinitelyPresentedSimpleGroup_iff.mpr (h G hfg (isMetabelianGroup_iff.mp hmet))

/-- Item (7) of Problem 5.3, from the development endpoint. -/
theorem finitely_presented_metabelian_embeds_in_finitely_presented_simple_of
    (h : GroupApproximation.BooneHigman.FinitelyGeneratedMetabelianStatement) :
    ∀ (G : Type) [Group G], Group.IsFinitelyPresented G → IsMetabelianGroup G →
      EmbedsInFinitelyPresentedSimpleGroup G := by
  intro G _ hfp hmet
  exact embedsInFinitelyPresentedSimpleGroup_iff.mpr
    (GroupApproximation.BooneHigman.finitelyPresentedMetabelianStatement_of_finitelyGenerated h
      G hfp (isMetabelianGroup_iff.mp hmet))

end MetabelianBooneHigman
