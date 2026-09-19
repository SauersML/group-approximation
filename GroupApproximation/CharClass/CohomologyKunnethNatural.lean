import GroupApproximation.CharClass.CohomologyKunnethSplit

/-!
# Naturality of the Künneth map in the base

A map `f : Y' → Y` induces `f × id : Y' × S^n → Y × S^n`, and the Künneth map

```text
(u, v) ↦ pr_Y^* u + (pr_S^* σ_n) ⌣ pr_Y^* v
```

commutes with it, because `f × id` commutes with the projection to the base and
**equals the identity** over the sphere factor, so it fixes the pulled-back
fundamental class.  This is the "natural in `Y`" half of the Künneth statement;
it needs nothing beyond `pull_comp` and three identities between continuous maps.

## Main declarations

* `knProdMap` — the induced map of products.
* `pull_knProdMap_knPrY`, `pull_knProdMap_knSigma` — the two naturality squares.
* `kunnethMap_natural` — the Künneth map is natural in the base.
-/

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {Y Y' : Type} [TopologicalSpace Y] [TopologicalSpace Y']

/-- The map `Y' × S^n → Y × S^n` induced by `f : Y' → Y`. -/
def knProdMap (f : C(Y', Y)) (n : ℕ) :
    TopCat.of (Y' × Sphere n) ⟶ TopCat.of (Y × Sphere n) :=
  cmap (f.prodMap (ContinuousMap.id (Sphere n)))

theorem knProdMap_comp_prY (f : C(Y', Y)) (n : ℕ) :
    knProdMap f n ≫ knPrY Y n = knPrY Y' n ≫ cmap f := rfl

theorem knProdMap_comp_prS (f : C(Y', Y)) (n : ℕ) :
    knProdMap f n ≫ knPrS Y n = knPrS Y' n := rfl

/-- **Naturality of the base projection.** -/
theorem pull_knProdMap_knPrY (f : C(Y', Y)) (n k : ℕ) (u : Hmod2 (TopCat.of Y) k) :
    pull (knProdMap f n) k (pull (knPrY Y n) k u)
      = pull (knPrY Y' n) k (pull (cmap f) k u) := by
  rw [← pull_comp, knProdMap_comp_prY, pull_comp]

/-- **The pulled-back fundamental class of the sphere factor is natural.** -/
theorem pull_knProdMap_knSigma (f : C(Y', Y)) (n : ℕ) (hn : 1 ≤ n) :
    pull (knProdMap f n) n (knSigma Y n hn) = knSigma Y' n hn := by
  rw [knSigma, knSigma, ← pull_comp, knProdMap_comp_prS]

/-- **The Künneth map is natural in the base.** -/
theorem kunnethMap_natural (f : C(Y', Y)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (u : Hmod2 (TopCat.of Y) (n + m)) (v : Hmod2 (TopCat.of Y) m) :
    pull (knProdMap f n) (n + m)
        (pull (knPrY Y n) (n + m) u + cup (knSigma Y n hn) (pull (knPrY Y n) m v))
      = pull (knPrY Y' n) (n + m) (pull (cmap f) (n + m) u)
        + cup (knSigma Y' n hn) (pull (knPrY Y' n) m (pull (cmap f) m v)) := by
  rw [pull_add, pull_knProdMap_knPrY, pull_cup, pull_knProdMap_knSigma, pull_knProdMap_knPrY]

end

end GroupApproximation.CharClass
