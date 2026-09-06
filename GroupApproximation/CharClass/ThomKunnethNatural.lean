import GroupApproximation.CharClass.CohomologyKunnethDecomp

/-!
# The Künneth decomposition is natural in the base

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C, hypothesis 6).

`cc-bundle`'s route to the Thom class of a trivial bundle replaces the punctured
fibre by a sphere and runs the long exact sequence of the pair against the
**absolute** Künneth decomposition, avoiding both a relative Künneth and any
contractibility assumption on the base.  It needs two facts about
`KnHemi.kunneth_decomposition`:

1. that the first summand is pullback along the projection — this is already how
   `cc-cohom-api` states the theorem, so there is nothing to prove;
2. that the decomposition is **natural in the base**, which is this file.

Naturality is short for the reason the decomposition is stated the way it is:
every term is built from `knPrY`, `knPrS` and `cup`, and a base map commutes with
both projections by `rfl`, so each term transports on its own.  No uniqueness
argument is needed.

## Main declarations

* `knBaseMap` — a base map crossed with the sphere.
* `knBaseMap_comp_knPrY`, `knBaseMap_comp_knPrS` — the two commuting squares.
* `knSigma_natural` — the sphere class is pulled back from the sphere, so it is
  invariant.
* `pull_knBaseMap_knPrY` — the first summand transports.
* `kunneth_decomposition_natural` — **the whole decomposition transports.**
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {Y Y' : Type} [TopologicalSpace Y] [TopologicalSpace Y']

/-- A base map crossed with the identity of the sphere factor. -/
def knBaseMap (f : C(Y', Y)) (n : ℕ) :
    TopCat.of (Y' × Sphere n) ⟶ TopCat.of (Y × Sphere n) :=
  cmap (f.prodMap (ContinuousMap.id (Sphere n)))

theorem knBaseMap_comp_knPrY (f : C(Y', Y)) (n : ℕ) :
    knBaseMap f n ≫ knPrY Y n = knPrY Y' n ≫ cmap f := rfl

theorem knBaseMap_comp_knPrS (f : C(Y', Y)) (n : ℕ) :
    knBaseMap f n ≫ knPrS Y n = knPrS Y' n := rfl

/-- **The sphere class is invariant.**  It is pulled back from the sphere factor,
which the base map leaves alone. -/
theorem knSigma_natural (f : C(Y', Y)) (n : ℕ) (hn : 1 ≤ n) :
    pull (knBaseMap f n) n (knSigma Y n hn) = knSigma Y' n hn := by
  rw [knSigma, knSigma, ← pull_comp, knBaseMap_comp_knPrS]

/-- **The first summand transports.** -/
theorem pull_knBaseMap_knPrY (f : C(Y', Y)) (n k : ℕ) (a : Hmod2 (TopCat.of Y) k) :
    pull (knBaseMap f n) k (pull (knPrY Y n) k a)
      = pull (knPrY Y' n) k (pull (cmap f) k a) := by
  rw [← pull_comp, knBaseMap_comp_knPrY, pull_comp]

/-- **The Künneth decomposition is natural in the base.**  Both coefficients pull
back, and the sphere class is unchanged. -/
theorem kunneth_decomposition_natural (f : C(Y', Y)) (n : ℕ) (hn : 1 ≤ n) (k m : ℕ)
    (hk : n + m = k) (a : Hmod2 (TopCat.of Y) k) (b : Hmod2 (TopCat.of Y) m) :
    pull (knBaseMap f n) k
        (pull (knPrY Y n) k a
          + cohCast hk (cup (knSigma Y n hn) (pull (knPrY Y n) m b)))
      = pull (knPrY Y' n) k (pull (cmap f) k a)
        + cohCast hk
            (cup (knSigma Y' n hn) (pull (knPrY Y' n) m (pull (cmap f) m b))) := by
  rw [pull_add, pull_knBaseMap_knPrY, KnHemi.pull_cohCast, pull_cup, knSigma_natural,
    pull_knBaseMap_knPrY]

end

end GroupApproximation.CharClass
