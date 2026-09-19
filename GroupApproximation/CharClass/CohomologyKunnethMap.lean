import GroupApproximation.CharClass.CohomologyKunnethNatural

/-!
# The Künneth map with a sphere factor, and the exact shape of what is left

This file names the Künneth map

```text
kunnethMap : H^{n+m}(Y; F₂) → H^m(Y; F₂) → H^{n+m}(Y × S^n; F₂),
  (u, v) ↦ pr_Y^* u + (pr_S^* σ_n) ⌣ pr_Y^* v
```

and reduces its injectivity to a **single** remaining statement, so that the
consumers can build against a named hypothesis rather than a gap.  The first
component is settled by `kunneth_fst_eq_zero`: a slice retracts `pr_Y^*` and kills
the sphere class.  The second is not, and cannot be, because a slice kills the
whole second term; it needs the Mayer–Vietoris connecting map's `H^*(X)`-linearity.

`KunnethSecondInjective Y n` is exactly that missing statement, and
`kunnethInjective_of_second` turns it into full injectivity.  A lane that needs
injectivity today should take `KunnethSecondInjective` as an explicit hypothesis;
the module then becomes unconditional the moment the lemma is proved, with no
restructuring.

## Main declarations

* `kunnethMap` — the map itself.
* `KunnethSecondInjective` — the one missing statement.
* `kunnethInjective_of_second` — first component plus the hypothesis gives both.
-/

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable (Y : Type) [TopologicalSpace Y] (n : ℕ)

/-- **The Künneth map with a sphere factor**,
`(u, v) ↦ pr_Y^* u + (pr_S^* σ_n) ⌣ pr_Y^* v`. -/
def kunnethMap (hn : 1 ≤ n) (m : ℕ) (u : Hmod2 (TopCat.of Y) (n + m))
    (v : Hmod2 (TopCat.of Y) m) : Hmod2 (TopCat.of (Y × Sphere n)) (n + m) :=
  pull (knPrY Y n) (n + m) u + cup (knSigma Y n hn) (pull (knPrY Y n) m v)

theorem kunnethMap_eq (hn : 1 ≤ n) (m : ℕ) (u : Hmod2 (TopCat.of Y) (n + m))
    (v : Hmod2 (TopCat.of Y) m) :
    kunnethMap Y n hn m u v
      = pull (knPrY Y n) (n + m) u + cup (knSigma Y n hn) (pull (knPrY Y n) m v) := rfl

/-- The one statement still missing for the Künneth isomorphism with a sphere
factor: cupping with the pulled-back fundamental class of the sphere is injective
on classes pulled back from the base. -/
def KunnethSecondInjective : Prop :=
  ∀ (hn : 1 ≤ n) (m : ℕ) (v : Hmod2 (TopCat.of Y) m),
    cup (knSigma Y n hn) (pull (knPrY Y n) m v) = 0 → v = 0

/-- **Injectivity of the Künneth map**, granted the second component.  The first
component is the slice argument `kunneth_fst_eq_zero`. -/
theorem kunnethInjective_of_second (p : Sphere n) (h : KunnethSecondInjective Y n)
    (hn : 1 ≤ n) (m : ℕ) (u : Hmod2 (TopCat.of Y) (n + m)) (v : Hmod2 (TopCat.of Y) m)
    (hz : kunnethMap Y n hn m u v = 0) : u = 0 ∧ v = 0 := by
  have hu : u = 0 := kunneth_fst_eq_zero Y n hn p m u v hz
  refine ⟨hu, h hn m v ?_⟩
  rw [kunnethMap_eq, hu, pull_zero, zero_add] at hz
  exact hz

end

end GroupApproximation.CharClass

/-!
## The route to `KunnethSecondInjective`

Cover the sphere factor by its two punctured hemispheres, both contractible, with
intersection the equatorial band, and cross the cover with `Y`
(`CohomologyProductCover`'s `prodOpen`).  In the resulting Mayer–Vietoris sequence
the class `(pr_S^* σ_n) ⌣ pr_Y^* v` is the image under the connecting map of
`τ ⌣ pr_Y^* v` restricted to the band, where `τ` is a class on the band with
`δ τ = pr_S^* σ_n`.  Making that identification is exactly

```text
δ (a ⌣ b|_{U ⊓ V}) = δ a ⌣ b        for a globally defined b,
```

whose proof is cochain-level: Mathlib's `ShortComplex.ShortExact.δ_eq` describes
`δ` as "lift along `g`, differentiate, descend along `f`", the lift is available
because `mvCoSC` is degreewise split (`mvCoSplitting`), and mod 2 the Leibniz rule
gives `d (x₂ ⌣ b) = d x₂ ⌣ b` for a cocycle `b`.  The work is transporting cup
products across `subCxDualIso` and assembling the degree-shifted morphism of short
complexes.
-/
