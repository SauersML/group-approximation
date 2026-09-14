/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The Boone–Higman statements for metabelian and linear groups

J. Belk, C. Bleak, F. Matucci and M. C. B. Zaremsky, *Progress around the Boone–Higman
conjecture*, arXiv:2306.16356v3 (22 May 2025), page 1, state the conjecture:

> A finitely generated group G has solvable word problem if and only if it embeds into some
> finitely presented simple group.

Problem 5.3 on page 17 asks for a proof of the conjecture for, among other classes,
"(7) Finitely presented metabelian groups".  Footnote 9 on the same page recalls that such groups
have solvable word problem.  One direction of the conjecture holds for every finitely generated
group (Kuznetsov, page 1), so for this class the content of item (7) is the embedding.

This module imports Mathlib only, so its definitions can be copied into a Palomar challenge.

* `IsMetabelianGroup G`: the second derived subgroup `⁅G', G'⁆` is trivial, that is, the derived
  length is at most two.  Abelian groups count as metabelian.
* `EmbedsInFinitelyPresentedSimpleGroup G`: some group `S : Type` that is finitely presented
  (Mathlib's `Group.IsFinitelyPresented`) and simple (Mathlib's `IsSimpleGroup`: nontrivial, and
  every normal subgroup is `⊥` or `⊤`) receives an injective homomorphism from `G`.
* `FinitelyPresentedMetabelianStatement` (T1): every finitely presented metabelian group embeds in
  a finitely presented simple group.  This is item (7) of Problem 5.3.
* `FinitelyGeneratedMetabelianStatement` (T2): the same for finitely generated metabelian groups.
  It implies T1 (`finitelyPresentedMetabelianStatement_of_finitelyGenerated`), and footnote 9
  (Baumslag–Remeslennikov) gives the converse.
* `FinitelyGeneratedLinearStatement` (T3): every finitely generated subgroup of `GL_n(K)`, for a
  field `K`, embeds in a finitely presented simple group.  Item (5) of Problem 5.3, `GL_n(ℚ)`, is
  the case `K = ℚ` for subgroups.

All groups and fields are quantified over `Type`.
-/

namespace GroupApproximation.BooneHigman

/-- A group is metabelian when its second derived subgroup `⁅G', G'⁆` is trivial. -/
def IsMetabelianGroup (G : Type*) [Group G] : Prop :=
  ⁅commutator G, commutator G⁆ = ⊥

/-- `G` embeds in a finitely presented simple group. -/
def EmbedsInFinitelyPresentedSimpleGroup (G : Type*) [Group G] : Prop :=
  ∃ (S : Type) (_ : Group S), Group.IsFinitelyPresented S ∧ IsSimpleGroup S ∧
    ∃ f : G →* S, Function.Injective f

/-- **T1**, item (7) of BBMZ Problem 5.3: every finitely presented metabelian group embeds in a
finitely presented simple group. -/
def FinitelyPresentedMetabelianStatement : Prop :=
  ∀ (G : Type) [Group G], Group.IsFinitelyPresented G → IsMetabelianGroup G →
    EmbedsInFinitelyPresentedSimpleGroup G

/-- **T2**: every finitely generated metabelian group embeds in a finitely presented simple
group. -/
def FinitelyGeneratedMetabelianStatement : Prop :=
  ∀ (G : Type) [Group G], Group.FG G → IsMetabelianGroup G →
    EmbedsInFinitelyPresentedSimpleGroup G

/-- **T3**: every finitely generated subgroup of `GL_n(K)`, for any field `K`, embeds in a finitely
presented simple group. -/
def FinitelyGeneratedLinearStatement : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)),
    H.FG → EmbedsInFinitelyPresentedSimpleGroup H

end GroupApproximation.BooneHigman
