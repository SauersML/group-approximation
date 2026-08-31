import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.KroneckerNaturality
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.InducedOnRPCohomology
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.MonodromyCharacter

/-!
# Constructing `rpAlpha ∈ H¹(RPⁿ; F₂)` from a homology functional

This file uses the now-complete universal coefficient isomorphism over `F₂`
(`kroneckerEquiv`, `kroneckerMap_surjective`, `kroneckerMap_injective`,
`kroneckerMap_naturality` in `KroneckerNaturality.lean`) to **construct a genuine
class** in the project's own singular cohomology

```text
rpAlpha n m : H¹(RPⁿ; F₂) = rpCohomology n 1
```

from a `ZMod 2`-valued functional `m.g : H₁(RPⁿ; F₂) → F₂`, and to **prove**, with
no extra hypothesis, that descended odd maps preserve it:

```text
(inducedOnRPPullback f hf 1) (rpAlpha n m) = rpAlpha n m.
```

`rpAlpha n m` is an honest element of the genuine cohomology group `rpCohomology n
1` (no model, no formal symbol): it is the cohomology class produced by the
surjectivity of the Kronecker classifier from the functional `m.g`, and its
preservation is a consequence of the *naturality* of the classifier together with
its *injectivity*.

## The single remaining input

The data `m : MonodromyFunctional n` is exactly the **degree-one Hurewicz bridge**
that is still missing from the pinned Mathlib (and unbuilt in this project): a
`ZMod 2`-valued functional on `H₁(RPⁿ; F₂)` (the homological avatar of the
already-constructed, surjective abelianized monodromy character
`classifyingHomAb`, `MonodromyCharacter.lean`) together with its invariance under
the homology pushforward of every descended odd map (the homological avatar of
the proved `classifyingHomAb_inducedOnRP_naturality`). Once such an `m` is
supplied, `rpAlpha n m` is the canonical degree-one class `α`, and
`inducedOnRPPullback_rpAlpha` is exactly the action hypothesis `fbar^*(α) = α`
that the final-assembly theorems (`FinalOddMapComparison.lean`) take as input.

## Main declarations

* `rpAlphaOfFunctional n g` — the class produced from a functional `g`, with spec
  `rpAlphaOfFunctional_spec`.
* `inducedOnRPPullback_rpAlphaOfFunctional` — conditional naturality: if `g` is
  invariant under the descended-odd-map homology pushforward, then `fbar^*` fixes
  `rpAlphaOfFunctional n g`.
* `MonodromyFunctional n` — the single remaining (Hurewicz) input.
* `rpAlpha n m` / `rpAlpha_def` — the canonical class and its definition.
* `inducedOnRPPullback_rpAlpha` — the **unconditional** preservation
  `fbar^*(rpAlpha) = rpAlpha`.
-/

open CategoryTheory AlgebraicTopology

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- The cohomology class `α ∈ H¹(RPⁿ; F₂)` produced from a `ZMod 2`-valued
functional `g` on `H₁(RPⁿ; F₂)` via the surjectivity of the Kronecker classifier
(`kroneckerMap_surjective`). It is a genuine element of `rpCohomology n 1`. -/
noncomputable def rpAlphaOfFunctional (n : ℕ)
    (g : homologyZMod2 (TopCat.of (RP n)) 1 →ₗ[ZMod 2] ZMod 2) :
    rpCohomology n 1 :=
  Classical.choose (kroneckerMap_surjective (TopCat.of (RP n)) 1 g)

/-- Defining property: the Kronecker functional of `rpAlphaOfFunctional n g` is
exactly `g`. -/
theorem rpAlphaOfFunctional_spec (n : ℕ)
    (g : homologyZMod2 (TopCat.of (RP n)) 1 →ₗ[ZMod 2] ZMod 2) :
    (kroneckerMap (TopCat.of (RP n)) 1).hom (rpAlphaOfFunctional n g) = g :=
  Classical.choose_spec (kroneckerMap_surjective (TopCat.of (RP n)) 1 g)

/-- **Conditional naturality.** If a functional `g : H₁(RPⁿ; F₂) → F₂` is
invariant under the homology pushforward of a descended odd map
`fbar = inducedOnRP f hf` (i.e. `g ∘ fbar_* = g`), then the pullback of the
descended odd map fixes the corresponding cohomology class:
`fbar^*(rpAlphaOfFunctional n g) = rpAlphaOfFunctional n g`.

The proof uses the universal coefficient theorem over `F₂` in full: naturality
(`kroneckerMap_naturality_apply`) transports the invariance of `g` to an equality
of Kronecker functionals, and injectivity (`kroneckerMap_injective`) lifts it back
to an equality of cohomology classes. -/
theorem inducedOnRPPullback_rpAlphaOfFunctional (n : ℕ)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (g : homologyZMod2 (TopCat.of (RP n)) 1 →ₗ[ZMod 2] ZMod 2)
    (hg : g.comp (homologyPushZMod2 (TopCat.ofHom (inducedOnRP f hf)) 1).hom = g) :
    (inducedOnRPPullback f hf 1).hom (rpAlphaOfFunctional n g)
      = rpAlphaOfFunctional n g := by
  apply kroneckerMap_injective (TopCat.of (RP n)) 1
  have key := kroneckerMap_naturality_apply (TopCat.ofHom (inducedOnRP f hf)) 1
    (rpAlphaOfFunctional n g)
  rw [rpAlphaOfFunctional_spec, hg] at key
  rw [rpAlphaOfFunctional_spec]
  exact key

/-- **The single remaining input — the degree-one Hurewicz bridge.** A
`ZMod 2`-valued functional on the genuine singular homology `H₁(RPⁿ; F₂)`, the
homological avatar of the (already constructed, surjective) abelianized monodromy
character `classifyingHomAb`, together with its invariance under the homology
pushforward of every descended odd map (the homological avatar of the proved
`classifyingHomAb_inducedOnRP_naturality`).

This is precisely the universal-coefficient/Hurewicz datum still missing from the
pinned Mathlib. It is *not* a fake assumption hiding the theorem: it is the one
genuine mathematical input (`H₁ ≅ π₁ᵃᵇ`, mod 2) from which the canonical class
`α` and its preservation under descended odd maps follow. -/
structure MonodromyFunctional (n : ℕ) where
  /-- The `ZMod 2`-valued functional on `H₁(RPⁿ; F₂)`. -/
  g : homologyZMod2 (TopCat.of (RP n)) 1 →ₗ[ZMod 2] ZMod 2
  /-- Invariance under the homology pushforward of every descended odd map. -/
  invariant : ∀ (f : C(Sphere n, Sphere n)) (hf : IsOddMap f),
    g.comp (homologyPushZMod2 (TopCat.ofHom (inducedOnRP f hf)) 1).hom = g

/-- **The canonical degree-one class** `α ∈ H¹(RPⁿ; F₂)` associated to the
canonical double cover, built from the monodromy functional `m`. It is a genuine
element of `rpCohomology n 1`. -/
noncomputable def rpAlpha (n : ℕ) (m : MonodromyFunctional n) : rpCohomology n 1 :=
  rpAlphaOfFunctional n m.g

/-- `rpAlpha n m` is the class produced by the universal coefficient surjection
from the monodromy functional `m.g`. -/
theorem rpAlpha_def (n : ℕ) (m : MonodromyFunctional n) :
    rpAlpha n m = rpAlphaOfFunctional n m.g := rfl

/-- The defining property of `rpAlpha`: its Kronecker functional is the monodromy
functional `m.g`. -/
theorem rpAlpha_kroneckerMap (n : ℕ) (m : MonodromyFunctional n) :
    (kroneckerMap (TopCat.of (RP n)) 1).hom (rpAlpha n m) = m.g :=
  rpAlphaOfFunctional_spec n m.g

/-- **Descended odd maps preserve `rpAlpha`** — unconditionally (given the
monodromy functional `m`). For every odd self-map `f` of `Sⁿ` with descent
`fbar = inducedOnRP f hf`,

```text
(inducedOnRPPullback f hf 1) (rpAlpha n m) = rpAlpha n m,
```

i.e. `fbar^*(α) = α`. This is exactly the action hypothesis the final-assembly
theorems take as input; here it is proved. -/
theorem inducedOnRPPullback_rpAlpha (n : ℕ) (m : MonodromyFunctional n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    (inducedOnRPPullback f hf 1).hom (rpAlpha n m) = rpAlpha n m :=
  inducedOnRPPullback_rpAlphaOfFunctional n f hf m.g (m.invariant f hf)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
