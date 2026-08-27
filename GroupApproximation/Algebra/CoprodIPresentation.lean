import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.CoprodI

/-!
# An indexed free product of presented groups is presented by the disjoint union

Mathlib has the binary statement, `PresentedGroup.coprodPresentations`:
`PresentedGroup R₁ ∗ PresentedGroup R₂` is presented on `α ⊕ β` by the
relators of the two factors, transported along the two injections, and by
nothing else.  This file is the indexed version, over an arbitrary index type
`ι`:

    ⨿_{i : ι} ⟨X i | R i⟩  ≅  ⟨ Σ i, X i | ⋃ i, (Sigma.mk i)_* (R i) ⟩ .

The proof is Mathlib's binary proof with `Sum` replaced by `Sigma`:
`PresentedGroup.toGroup` one way, `Monoid.CoprodI.lift` of the
`PresentedGroup.map`s the other, and the two round trips checked on
generators.

## Why this is here

The point is the *absence* of cross relators, and that is what makes the
indexed statement worth having separately.  A presentation of the restricted
direct product `⨁ᵢ Gᵢ` on the same generating set needs, besides `⋃ᵢ Rᵢ`, the
commutators `[x, y]` for every pair of generators from two distinct factors
--- a second family, quadratic in the generators.  The free product needs
none: its relator set is the disjoint union of the factors' relator sets and
stops there.

`Monsters.ChiodoFreeProductAbsorber` uses this at
`ι := Monsters.FinitePresentationCode`, where each `(X c, R c)` is read
literally off the code `c`, to exhibit a presentation of the ambient free
product whose generator type is `Σ c, Fin c.1` and whose relator set is the
union of the codes' own relator sets.  That is the presentation Chiodo's
Proposition 3.8 --- the effective torsion-free quotient --- would be applied
to, and the reason the free product rather than the direct sum is the right
carrier for the recursive-presentation question.  Nothing here says anything
about computability; it supplies the presentation, not its recursiveness.
-/

namespace GroupApproximation
namespace CoprodIPresentation

open Monoid

universe u v

variable {ι : Type u} {α : ι → Type v} (rels : ∀ i, Set (FreeGroup (α i)))

/-! ## 1.  The relator set of the free product -/

/-- The `i`-th block inclusion of generating types,
`α i → Σ i, α i`. -/
def blockInj (i : ι) : α i → (Σ i, α i) := fun a ↦ ⟨i, a⟩

/-- The relators of an indexed free product presentation: the relators of
each factor, pushed into the free group on the disjoint union of the
generating types, and **nothing else**. -/
def coprodRels : Set (FreeGroup (Σ i, α i)) :=
  ⋃ i, FreeGroup.map (blockInj i) '' rels i

theorem mem_coprodRels {i : ι} {r : FreeGroup (α i)} (hr : r ∈ rels i) :
    FreeGroup.map (blockInj i) r ∈ coprodRels rels :=
  Set.mem_iUnion.2 ⟨i, ⟨r, hr, rfl⟩⟩

/-! ## 2.  The two maps -/

/-- The canonical map from the disjoint union of the generating types into
the indexed free product of the presented groups. -/
def toCoprodI : (Σ i, α i) → CoprodI (fun i ↦ PresentedGroup (rels i)) :=
  fun x ↦ CoprodI.of (i := x.1) (PresentedGroup.of (rels := rels x.1) x.2)

/-- On the `i`-th block of generators, the lift of `toCoprodI` is the
composite of the `i`-th presentation map with the `i`-th free factor
inclusion. -/
theorem lift_toCoprodI_comp_map (i : ι) :
    (FreeGroup.lift (toCoprodI rels)).comp (FreeGroup.map (blockInj i)) =
      (CoprodI.of (i := i)).comp (PresentedGroup.mk (rels i)) :=
  FreeGroup.ext_hom _ _ fun _ ↦ rfl

/-- The relators of the free product die in the free product: each of them is
a relator of one factor, and dies there. -/
theorem lift_toCoprodI_eq_one (r : FreeGroup (Σ i, α i))
    (hr : r ∈ coprodRels rels) : FreeGroup.lift (toCoprodI rels) r = 1 := by
  unfold coprodRels at hr
  simp only [Set.mem_iUnion, Set.mem_image] at hr
  obtain ⟨i, s, hs, rfl⟩ := hr
  have hstep : FreeGroup.lift (toCoprodI rels) (FreeGroup.map (blockInj i) s) =
      CoprodI.of (M := fun j ↦ PresentedGroup (rels j)) (i := i)
        (PresentedGroup.mk (rels i) s) := by
    rw [← MonoidHom.comp_apply, lift_toCoprodI_comp_map rels i, MonoidHom.comp_apply]
  rw [hstep, PresentedGroup.one_of_mem hs, map_one]

/-! ## 3.  The isomorphism -/

/-- **An indexed free product of presented groups is the presented group on
the disjoint union of the generators against the disjoint union of the
relators.**  The indexed form of `PresentedGroup.coprodPresentations`.

There are no cross relators: the relator set is `coprodRels`, and
`coprodRels` is a union over the index type of the factors' own relators. -/
def coprodIPresentation :
    PresentedGroup (coprodRels rels) ≃*
      CoprodI (fun i ↦ PresentedGroup (rels i)) :=
  MonoidHom.toMulEquiv
    (PresentedGroup.toGroup (lift_toCoprodI_eq_one rels))
    (CoprodI.lift fun i ↦
      PresentedGroup.map (FreeGroup.map (blockInj i))
        (fun _ hr ↦ mem_coprodRels rels hr))
    (PresentedGroup.ext fun x ↦ by cases x; rfl)
    (CoprodI.ext_hom _ _ fun _ ↦ PresentedGroup.ext fun _ ↦ rfl)

@[simp]
theorem coprodIPresentation_of (x : Σ i, α i) :
    coprodIPresentation rels (PresentedGroup.of x) =
      CoprodI.of (i := x.1) (PresentedGroup.of (rels := rels x.1) x.2) :=
  PresentedGroup.toGroup.of (lift_toCoprodI_eq_one rels)

end CoprodIPresentation
end GroupApproximation
