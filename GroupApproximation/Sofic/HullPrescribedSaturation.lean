import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.OrderOfElement

/-!
# Prescribed-subgroup saturation through two quotient stages

This file isolates the purely algebraic step in the prescribed-normal-subgroup
version of Hull's two-stage common-quotient construction.  No hyperbolicity,
small cancellation, or literature theorem occurs here.

Suppose the first stage gives maps

```
G₁ → M ← G₂
```

and routes the image of `G₁` into the image of a prescribed subgroup
`D ≤ G₂`.  If a second map `M → Q` makes the composite from `G₁`
surjective, then the composite from `D` is surjective as well.  This is the
exact algebra behind the substitution of target words chosen inside `D`:
stage one supplies the containment, and stage two supplies surjectivity.

The statement deliberately does not assume that `D` is normal.  Normality and
infinitude are needed to obtain the geometric suitability used to construct
the first stage, but they play no role once its image containment is known.
-/

namespace GroupApproximation
namespace HullPrescribedSaturation

/-! ## Permanence through successive quotient stages -/

/-- Hull's finite-order lifting conclusion composes.  This is the exact
torsion-control needed when a common quotient is followed by the prescribed
normal-saturation quotient: a finite-order element of the final group first
lifts through the second stage and then through the first, without replacing
Hull's conclusion by global order preservation. -/
theorem finiteOrder_lifts_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    (first : G →* H) (second : H →* K)
    (hfirst : ∀ (y : H) (n : ℕ), 0 < n → orderOf y = n →
      ∃ x : G, orderOf x = n ∧ first x = y)
    (hsecond : ∀ (z : K) (n : ℕ), 0 < n → orderOf z = n →
      ∃ y : H, orderOf y = n ∧ second y = z) :
    ∀ (z : K) (n : ℕ), 0 < n → orderOf z = n →
      ∃ x : G, orderOf x = n ∧ (second.comp first) x = z := by
  intro z n hn hz
  obtain ⟨y, hyOrder, hy⟩ := hsecond z n hn hz
  obtain ⟨x, hxOrder, hx⟩ := hfirst y n hn hyOrder
  exact ⟨x, hxOrder, by simp only [MonoidHom.comp_apply, hx, hy]⟩

/-- Injectivity on a protected set also composes, provided the second stage is
injective on the image protected by the first.  This is the literal protected-
ball bookkeeping for two successive Hull quotients. -/
theorem injOn_comp
    {G H K : Type*} [Group G] [Group H] [Group K]
    (first : G →* H) (second : H →* K) (S : Set G)
    (hfirst : Set.InjOn first S)
    (hsecond : Set.InjOn second (first '' S)) :
    Set.InjOn (second.comp first) S := by
  intro x hx y hy hxy
  apply hfirst hx hy
  apply hsecond ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  simpa only [MonoidHom.comp_apply] using hxy

variable {G₁ G₂ M Q : Type*}
  [Group G₁] [Group G₂] [Group M] [Group Q]

/-- **Two-stage prescribed-subgroup saturation.**

If the first-factor image in `M` is contained in the image of `D ≤ G₂`,
and the second quotient is onto when restricted to that first-factor image,
then `D` maps onto the final quotient.

In the common-quotient application, `first` and `second` are the two factor
maps after Hull's first quotient, `finish` is Hull's second quotient,
`hroute` is Theorem 7.1(c) with target words selected in `D`, and `hfinish`
is the second application of the same routing clause.  Only `hroute` and
`hfinish` remain for the small-cancellation layer to prove. -/
theorem map_eq_top_of_range_le_map_of_comp_surjective
    (D : Subgroup G₂) (first : G₁ →* M) (second : G₂ →* M)
    (finish : M →* Q)
    (hroute : first.range ≤ D.map second)
    (hfinish : Function.Surjective (finish.comp first)) :
    D.map (finish.comp second) = ⊤ := by
  rw [eq_top_iff]
  intro q _
  obtain ⟨x, hx⟩ := hfinish q
  have hfirst : first x ∈ first.range := ⟨x, rfl⟩
  obtain ⟨d, hd, hdEq⟩ := Subgroup.mem_map.mp (hroute hfirst)
  refine Subgroup.mem_map.mpr ⟨d, hd, ?_⟩
  calc
    (finish.comp second) d = finish (second d) := rfl
    _ = finish (first x) := congrArg finish hdEq
    _ = q := hx

end HullPrescribedSaturation
end GroupApproximation
