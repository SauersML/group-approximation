import Mathlib.GroupTheory.HNNExtension
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.PushoutI

/-!
# Stage E6, forward half: a presented HNN tower maps to the honest one

Stage **E6** of the Adian--Rabin roadmap in
`GroupApproximation/Computability/RabinConstruction.lean` asks to identify a
group given by HNN relations with `HNNExtension`, and one given by amalgamation
relations with `PushoutI`.  The roadmap notes that **only the forward map is
strictly needed**:

> to conclude `E ↪ K(w)` it is enough to have a homomorphism `K(w) →* J` into
> the honest tower `J` whose restriction along `E → K(w)` is the known
> injection `E → J`.

This file supplies that direction, in general form, for both constructions.
The reverse identifications — that the presented group *is* the HNN extension
or the pushout — are not needed for the embedding and are not attempted.

## Why the forward direction is easy and the reverse is not

A presented group maps *out* by its universal property: assign a target to each
generator and check every relator dies.  So the entire content is that the
displayed HNN relator, in conjugation form, holds in `HNNExtension`, which is
`HNNExtension.equiv_eq_conj`, and that the displayed amalgamation relator holds
in `PushoutI`, which is `PushoutI.of_apply_eq_base`.

The reverse direction would need a map *into* the presented group, that is, a
normal form for it — which is exactly what the presentation does not hand you,
and why the roadmap flags E6 as the expensive stage. Not needing it halves the
stage.

## The shape of the relators

An HNN relator is `t a t⁻¹ (φ a)⁻¹` for `a` ranging over a generating set of
the associated subgroup.  Checking it on generators suffices for the map to
exist, because a homomorphism out of the presented group only sees the relators
it is handed; that the relation then holds on the whole associated subgroup is
automatic in the target, being a statement about `φ` there.

Never compiled.
-/

namespace GroupApproximation
namespace HNNPresentedForward

open HNNExtension

/-! ## The HNN forward map -/

variable {G : Type*} [Group G] {A B : Subgroup G} (φ : A ≃* B)

/-- The generator assignment: the base generators go to the base, and the
stable letter to the stable letter. -/
def hnnGen {α : Type*} (g : α → G) : α ⊕ Unit → HNNExtension G A B φ
  | Sum.inl a => HNNExtension.of (g a)
  | Sum.inr () => HNNExtension.t

@[simp] theorem hnnGen_inl {α : Type*} (g : α → G) (a : α) :
    hnnGen φ g (Sum.inl a) = HNNExtension.of (g a) := rfl

@[simp] theorem hnnGen_inr {α : Type*} (g : α → G) :
    hnnGen φ g (Sum.inr ()) = HNNExtension.t := rfl

/-- **The displayed HNN relator holds in the HNN extension.**  This is the one
fact the forward map needs, and it is `equiv_eq_conj` rearranged: conjugating
an element of the associated subgroup by the stable letter is its image. -/
theorem hnn_relator (a : A) :
    HNNExtension.t * HNNExtension.of (a : G) * HNNExtension.t⁻¹ *
      (HNNExtension.of (φ a : G))⁻¹ = (1 : HNNExtension G A B φ) := by
  rw [← HNNExtension.equiv_eq_conj]
  exact mul_inv_cancel _

/-- The same relator in the form a relator set carries it: as an equation
between the two conjugates. -/
theorem hnn_conj_eq (a : A) :
    HNNExtension.t * HNNExtension.of (a : G) * HNNExtension.t⁻¹
      = (HNNExtension.of (φ a : G) : HNNExtension G A B φ) :=
  -- `equiv_eq_conj` takes the subgroup element, not the equivalence, so it is
  -- read off `hnn_relator` instead: `x * y⁻¹ = 1` is `x = y`.
  mul_inv_eq_one.mp (hnn_relator φ a)

/-! ## The amalgamation forward map -/

section Pushout

variable {ι : Type*} {H : Type*} [Group H] {K : ι → Type*} [∀ i, Group (K i)]
  (ψ : ∀ i, H →* K i)

/-- **The displayed amalgamation relator holds in the pushout.**  Two vertex
groups agree on the amalgamated subgroup, which is `of_apply_eq_base` twice. -/
theorem pushout_relator (i j : ι) (x : H) :
    Monoid.PushoutI.of (φ := ψ) i (ψ i x)
      = Monoid.PushoutI.of (φ := ψ) j (ψ j x) := by
  rw [Monoid.PushoutI.of_apply_eq_base, Monoid.PushoutI.of_apply_eq_base]

end Pushout

/-! ## What this gives the Rabin assembly

`K(w)` is a presented group.  Its relators are, in order: the source relators,
the `t`-layer HNN relators, the `u`-layer HNN relator, the two
Baumslag--Solitar relators of `G₂`, and the two amalgamation identifications
`u = a` and `c = [w, s₀]`.

Against the honest tower `J`, built as an iterated `HNNExtension` and one
`PushoutI`, every one of those relators dies:

* source relators, because the base of the tower is the source group and they
  hold there;
* the two HNN layers, by `hnn_conj_eq`;
* the `G₂` relators, likewise, that factor being itself an iterated HNN
  extension;
* the two identifications, by `pushout_relator`.

So `PresentedGroup.toGroup` produces `K(w) →* J`, and stage **E7** is then the
observation that the composite `E → K(w) → J` is the known injection `E → J`,
whence `E → K(w)` is injective — no reverse identification anywhere.

What is still owed before that assembly can be written down is the tower `J`
itself, which needs the associated-subgroup isomorphisms: `FreeGroupSquaring`
supplies the one between the stable letters and their squares, and the two
rank-two free subgroups are the named targets of `RabinBrittonFreeness`.
-/

end HNNPresentedForward
end GroupApproximation
