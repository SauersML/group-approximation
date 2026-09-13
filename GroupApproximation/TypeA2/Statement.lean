/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Fournier-Facio–Wu–Zaremsky Question 5.8: definitions and statement

F. Fournier-Facio, X. Wu and M. C. B. Zaremsky, *Abstract twisted Brin–Thompson
groups*, arXiv:2603.24687v2, p. 27:

> **Question 5.8.** Does there exist an example of a group action `G ↷ S` that is
> of type [A₂] such that `G/ker(G ↷ S)` is not finitely presented?

A parenthetical adds that this amounts to the induced action of the quotient on `S`
not being of type (A₂).  On p. 25 the authors say they know no explicit example.

## Definition 1.3 (pp. 2–3), at `n = 2`

FFWZ let a group `G` act on a non-empty set `S`.  The action is of type [Aₙ] when:
(i) `G` is of type `Fₙ`;
(ii) `Stab_G(T)` is of type `F_{n-|T|}` for every finite `T ⊆ S`;
(iii) the diagonal action of `G` on `Sⁿ` has finitely many orbits.
A faithful action of type [Aₙ] is of type (Aₙ).  They note (p. 3) that [Zar24] mostly
called type (A₂) "type (A)".

§1.2 records that every group is of type `F₀`, that type `F₁` is finite generation,
and that type `F₂` is finite presentability.  Page 3 adds that condition (ii) is empty
when `|T| ≥ n`.  So for `n = 2`:
* (i) says `G` is finitely presented;
* (ii) repeats (i) at `T = ∅`, says `Stab_G(s)` is finitely generated at `T = {s}`,
  and says nothing when `|T| ≥ 2`;
* (iii) says `G` has finitely many orbits on `S × S`.

## Conventions

* `S` is a set (a `Type`), non-empty as in Definition 1.3.  Type [A₂] does not assume
  faithfulness.
* An action is Mathlib's `MulAction`, a left action.
* Finite presentation is Mathlib's `Group.IsFinitelyPresented`: some surjection from a
  free group of finite rank whose kernel is finitely normally generated.
* `ker(G ↷ S)` is the kernel of `MulAction.toPermHom G S : G →* Equiv.Perm S`.
* Groups and sets live in `Type`.

## Contents

* `IsTypeA2` and `actionKernel` form the shared block of the Palomar pair
  `Palomar/TypeA2Challenge.lean` / `Palomar/TypeA2Solution.lean`.
* `IsTypeParenA2` is type (A₂).  The statement does not use it.
* `Question58` is the positive answer, as a `Prop`.
* `mem_actionKernel` and `finite_orbitRel_quotient_iff` are interface lemmas.

The model tests are in `GroupApproximation.TypeA2.StatementModels`.

The prose of this module was written by Claude (Anthropic).
-/

namespace GroupApproximation.TypeA2

-- BEGIN SHARED BLOCK (kept byte-identical in `Palomar/TypeA2Challenge.lean` and `Palomar/TypeA2Solution.lean`)

/-- An action of `G` on `S` of **type [A₂]** (FFWZ Definition 1.3, `n = 2`): `S` is
non-empty, `G` is finitely presented, every point stabilizer is finitely generated,
and the diagonal action of `G` on `S × S` has finitely many orbits.  The action need
not be faithful. -/
def IsTypeA2 (G S : Type) [Group G] [MulAction G S] : Prop :=
  Nonempty S ∧ Group.IsFinitelyPresented G ∧ (∀ s : S, (MulAction.stabilizer G s).FG) ∧
    Finite (MulAction.orbitRel.Quotient G (S × S))

/-- The kernel `ker(G ↷ S)` of an action: the kernel of `G →* Equiv.Perm S`, that is,
the elements of `G` that fix every point of `S`. -/
abbrev actionKernel (G S : Type) [Group G] [MulAction G S] : Subgroup G :=
  (MulAction.toPermHom G S).ker

-- END SHARED BLOCK

/-- **FFWZ Question 5.8, positive answer**, as a `Prop`: some action `G ↷ S` of type
[A₂] has `G ⧸ ker(G ↷ S)` not finitely presented.  The Palomar theorem states this
body verbatim. -/
def Question58 : Prop :=
  ∃ (G : Type) (_ : Group G) (S : Type) (_ : MulAction G S),
    IsTypeA2 G S ∧ ¬ Group.IsFinitelyPresented (G ⧸ actionKernel G S)

/-- An action of **type (A₂)** (FFWZ Definition 1.3): of type [A₂] and faithful. -/
def IsTypeParenA2 (G S : Type) [Group G] [MulAction G S] : Prop :=
  IsTypeA2 G S ∧ FaithfulSMul G S

/-- Membership in `ker(G ↷ S)`: `g` fixes every point of `S`. -/
theorem mem_actionKernel {G S : Type} [Group G] [MulAction G S] {g : G} :
    g ∈ actionKernel G S ↔ ∀ s : S, g • s = s :=
  ⟨fun h s => DFunLike.congr_fun (MonoidHom.mem_ker.mp h) s,
    fun h => MonoidHom.mem_ker.mpr (Equiv.ext h)⟩

/-- Finitely many orbits, in representative form: some finite set of points meets
every orbit.  Condition (iii) of `IsTypeA2` is the case `X = S × S`. -/
theorem finite_orbitRel_quotient_iff {G X : Type*} [Group G] [MulAction G X] :
    Finite (MulAction.orbitRel.Quotient G X) ↔
      ∃ F : Finset X, ∀ x : X, ∃ f ∈ F, ∃ g : G, g • f = x := by
  constructor
  · intro hfin
    classical
    let _ : Fintype (MulAction.orbitRel.Quotient G X) := Fintype.ofFinite _
    refine ⟨Finset.univ.image (fun q : MulAction.orbitRel.Quotient G X => Quotient.out q),
      fun x => ⟨Quotient.out (Quotient.mk (MulAction.orbitRel G X) x),
        Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩⟩
    have h : x ∈ MulAction.orbit G (Quotient.out (Quotient.mk (MulAction.orbitRel G X) x)) :=
      Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G X) x)).symm
    exact MulAction.mem_orbit_iff.mp h
  · rintro ⟨F, hF⟩
    refine Finite.of_surjective
      (fun f : F => (Quotient.mk (MulAction.orbitRel G X) f.1 : MulAction.orbitRel.Quotient G X))
      fun q => ?_
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    obtain ⟨f, hf, g, hg⟩ := hF x
    refine ⟨⟨f, hf⟩, ?_⟩
    have h : f ∈ MulAction.orbit G x := MulAction.mem_orbit_iff.mpr ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
    show Quotient.mk (MulAction.orbitRel G X) f = Quotient.mk (MulAction.orbitRel G X) x
    exact Quotient.sound h

end GroupApproximation.TypeA2
