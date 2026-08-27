import GroupApproximation.Computability.RabinConstruction

/-!
# The source group of the Adian--Rabin construction: free products of presentations

Stage 1 of the Adian--Rabin construction (see `Computability.RabinConstruction`)
does not start from a group `H` with undecidable word problem alone.  It starts
from the free product `H * F`, where `F` is the *forbidden* group of the Markov
property --- for the manuscript's instance, this repository's finitely presented
non-MF group `E`.  The forbidden group has to be a free factor of the source,
because that is the only route by which it ends up inside `K(w)`:

```
E ↪ H * E ↪ G ↪ G' ↪ G'' ↪ K(w).
```

This file supplies the **first link** of that chain and the fact that makes the
enlarged source a legitimate input to the reduction.  Both are consequences of
`PresentedGroup.coprodPresentations`, which Mathlib already proves: the group
presented by the disjoint union of two presentations *is* the free product of
the two presented groups.

## What is proved

For relator sets `rels₁ ⊆ FreeGroup α` and `rels₂ ⊆ FreeGroup β`, writing
`K = ⟨α ⊔ β | rels₁ ⊔ rels₂⟩` for the free product presentation:

* `inclLeft_injective`, `inclRight_injective` --- **each factor embeds in the
  free product.**  With `β` naming the generators of `E`, this is `E ↪ H * E`.
* `mk_map_inl_eq_one_iff`, `mk_map_inr_eq_one_iff` --- **the word problem of
  each factor is exactly the restriction of the word problem of the free
  product.**  A word in the letters of one factor is trivial in the free
  product if and only if it is trivial in that factor.  The map on words is
  `FreeGroup.map Sum.inl`, a relabelling of letters, so this is a reduction in
  both directions and it is patently computable once the coding layer of
  `Computability.PresentationCodes` is in place.
* `coprodPresented_isFinitelyPresented` --- the free product of two finite
  presentations is a finite presentation.

The second item is the coordination fact for the Novikov--Boone lane.  What
that lane owes is undecidability of the word problem of `H * E`, and
`mk_map_inl_eq_one_iff` reduces it to undecidability for `H` alone with no
further group theory.  Nothing here asserts that any such `H` exists; no
statement in this file has a hypothesis, and none is conditional on anything.

## What is not proved

This is the *first* link only.  Links two through five --- `H * E ↪ G` (a
Tietze change of free basis), and the three HNN/amalgam inclusions --- are the
open steps E1 and E3--E7 listed in the roadmap in the module docstring of
`Computability.RabinConstruction`.
-/

namespace GroupApproximation
namespace RabinConstructionSource

open RabinConstruction

variable {α β : Type}

/-! ## The free product presentation -/

/-- The relator set of the free product presentation: the two relator sets,
relabelled into the disjoint union of the alphabets.  This is the exact shape
consumed by `PresentedGroup.coprodPresentations`. -/
abbrev coprodRels (rels₁ : Set (FreeGroup α)) (rels₂ : Set (FreeGroup β)) :
    Set (FreeGroup (α ⊕ β)) :=
  FreeGroup.map Sum.inl '' rels₁ ∪ FreeGroup.map Sum.inr '' rels₂

/-- The group presented by the disjoint union of the two presentations. -/
abbrev CoprodPresented (rels₁ : Set (FreeGroup α)) (rels₂ : Set (FreeGroup β)) :
    Type :=
  PresentedGroup (coprodRels rels₁ rels₂)

/-- **The free product presentation presents the free product.**  This is
Mathlib's `PresentedGroup.coprodPresentations`, named here for readability. -/
def coprodEquiv (rels₁ : Set (FreeGroup α)) (rels₂ : Set (FreeGroup β)) :
    CoprodPresented rels₁ rels₂ ≃*
      Monoid.Coprod (PresentedGroup rels₁) (PresentedGroup rels₂) :=
  PresentedGroup.coprodPresentations rels₁ rels₂

theorem coprodEquiv_mk (rels₁ : Set (FreeGroup α)) (rels₂ : Set (FreeGroup β))
    (x : FreeGroup (α ⊕ β)) :
    coprodEquiv rels₁ rels₂ (PresentedGroup.mk _ x) =
      FreeGroup.lift (PresentedGroup.toCoprod rels₁ rels₂) x :=
  presented_toGroup_mk (PresentedGroup.lift_toCoprod_eq_one rels₁ rels₂) x

theorem coprodEquiv_mk_map_inl (rels₁ : Set (FreeGroup α))
    (rels₂ : Set (FreeGroup β)) (v : FreeGroup α) :
    coprodEquiv rels₁ rels₂ (PresentedGroup.mk _ (FreeGroup.map Sum.inl v)) =
      Monoid.Coprod.inl (PresentedGroup.mk rels₁ v) := by
  rw [coprodEquiv_mk]
  exact DFunLike.congr_fun
    (PresentedGroup.lift_toCoprod_inl_eq_inl_mk rels₁ rels₂) v

theorem coprodEquiv_mk_map_inr (rels₁ : Set (FreeGroup α))
    (rels₂ : Set (FreeGroup β)) (v : FreeGroup β) :
    coprodEquiv rels₁ rels₂ (PresentedGroup.mk _ (FreeGroup.map Sum.inr v)) =
      Monoid.Coprod.inr (PresentedGroup.mk rels₂ v) := by
  rw [coprodEquiv_mk]
  exact DFunLike.congr_fun
    (PresentedGroup.lift_toCoprod_inr_eq_inr_mk rels₁ rels₂) v

/-- The free product of two finite presentations is a finite presentation. -/
theorem coprodPresented_isFinitelyPresented [Finite α] [Finite β]
    (R₁ : Finset (FreeGroup α)) (R₂ : Finset (FreeGroup β)) :
    Group.IsFinitelyPresented
      (CoprodPresented ((R₁ : Finset (FreeGroup α)) : Set (FreeGroup α))
        ((R₂ : Finset (FreeGroup β)) : Set (FreeGroup β))) :=
  Group.IsFinitelyPresented.equiv
    (coprodEquiv ((R₁ : Finset (FreeGroup α)) : Set (FreeGroup α))
      ((R₂ : Finset (FreeGroup β)) : Set (FreeGroup β))).symm

/-! ## Each factor embeds -/

/-- The inclusion of the left factor into the free product presentation. -/
def inclLeft (rels₁ : Set (FreeGroup α)) (rels₂ : Set (FreeGroup β)) :
    PresentedGroup rels₁ →* CoprodPresented rels₁ rels₂ :=
  ((coprodEquiv rels₁ rels₂).symm.toMonoidHom).comp Monoid.Coprod.inl

/-- The inclusion of the right factor into the free product presentation. -/
def inclRight (rels₁ : Set (FreeGroup α)) (rels₂ : Set (FreeGroup β)) :
    PresentedGroup rels₂ →* CoprodPresented rels₁ rels₂ :=
  ((coprodEquiv rels₁ rels₂).symm.toMonoidHom).comp Monoid.Coprod.inr

/-- **The left factor embeds in the free product.** -/
theorem inclLeft_injective (rels₁ : Set (FreeGroup α))
    (rels₂ : Set (FreeGroup β)) :
    Function.Injective (inclLeft rels₁ rels₂) := by
  intro x y hxy
  have h : (coprodEquiv rels₁ rels₂).symm (Monoid.Coprod.inl x) =
      (coprodEquiv rels₁ rels₂).symm (Monoid.Coprod.inl y) := hxy
  exact Monoid.Coprod.inl_injective ((coprodEquiv rels₁ rels₂).symm.injective h)

/-- **The right factor embeds in the free product.**  With `β` naming the
generators of the manuscript's finitely presented non-MF group `E` and `α`
those of a group with undecidable word problem, this is the first link
`E ↪ H * E` of the embedding chain. -/
theorem inclRight_injective (rels₁ : Set (FreeGroup α))
    (rels₂ : Set (FreeGroup β)) :
    Function.Injective (inclRight rels₁ rels₂) := by
  intro x y hxy
  have h : (coprodEquiv rels₁ rels₂).symm (Monoid.Coprod.inr x) =
      (coprodEquiv rels₁ rels₂).symm (Monoid.Coprod.inr y) := hxy
  exact Monoid.Coprod.inr_injective ((coprodEquiv rels₁ rels₂).symm.injective h)

/-! ## The word problem of a factor is the restriction of the word problem -/

/-- **A left-factor word is trivial in the free product exactly when it is
trivial in the left factor.** -/
theorem mk_map_inl_eq_one_iff (rels₁ : Set (FreeGroup α))
    (rels₂ : Set (FreeGroup β)) (v : FreeGroup α) :
    PresentedGroup.mk (coprodRels rels₁ rels₂) (FreeGroup.map Sum.inl v) = 1 ↔
      PresentedGroup.mk rels₁ v = 1 := by
  constructor
  · intro h
    refine Monoid.Coprod.inl_injective (N := PresentedGroup rels₂) ?_
    rw [← coprodEquiv_mk_map_inl rels₁ rels₂ v, h, map_one, map_one]
  · intro h
    refine (coprodEquiv rels₁ rels₂).injective ?_
    rw [coprodEquiv_mk_map_inl rels₁ rels₂ v, h, map_one, map_one]

/-- **A right-factor word is trivial in the free product exactly when it is
trivial in the right factor.** -/
theorem mk_map_inr_eq_one_iff (rels₁ : Set (FreeGroup α))
    (rels₂ : Set (FreeGroup β)) (v : FreeGroup β) :
    PresentedGroup.mk (coprodRels rels₁ rels₂) (FreeGroup.map Sum.inr v) = 1 ↔
      PresentedGroup.mk rels₂ v = 1 := by
  constructor
  · intro h
    refine Monoid.Coprod.inr_injective (M := PresentedGroup rels₁) ?_
    rw [← coprodEquiv_mk_map_inr rels₁ rels₂ v, h, map_one, map_one]
  · intro h
    refine (coprodEquiv rels₁ rels₂).injective ?_
    rw [coprodEquiv_mk_map_inr rels₁ rels₂ v, h, map_one, map_one]

end RabinConstructionSource
end GroupApproximation
