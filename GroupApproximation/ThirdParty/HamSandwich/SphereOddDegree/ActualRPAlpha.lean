import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnMonodromyFunctional

/-!
# The actual canonical class `actualRPAlpha n ∈ H¹(RPⁿ; F₂)` and its naturality

This file completes Prompt 19 for the `RPnGeneratorIdentification n` branch. With
the genuine `monodromyFunctional n : MonodromyFunctional n` now constructed (from
the actual double-cover monodromy / first Stiefel–Whitney class `rpW1Class n`, see
`RPnMonodromyFunctional.lean`), we can fix a single canonical degree-one class

```text
actualRPAlpha n : rpCohomology n 1
```

that no longer depends on an *arbitrary* `m : MonodromyFunctional n`, and prove
its preservation under descended odd maps.

## Main declarations

* `actualRPAlpha n` — the canonical class `rpAlpha n (monodromyFunctional n)`.
* `actualRPAlpha_eq_rpAlpha` — `actualRPAlpha n = rpAlpha n (monodromyFunctional n)`.
* `actualRPAlpha_eq_rpAlphaW1` — `actualRPAlpha n = rpAlphaW1 n`.
* `actualRPAlpha_kroneckerMap` — its Kronecker functional is `w1Functional n`.
* `inducedOnRPPullback_actualRPAlpha` — **the naturality / preservation theorem**:
  every descended odd map fixes `actualRPAlpha n`.
* `actualRPAlpha_preserved_by_inducedOnRP` — the same statement, named for
  downstream use.
-/

open CategoryTheory AlgebraicTopology

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **The actual canonical degree-one class** `α = w₁ ∈ H¹(RPⁿ; F₂)`, built from
the genuine constructed monodromy functional `monodromyFunctional n` (the Kronecker
dual of the first Stiefel–Whitney class of the double cover). Unlike `rpAlpha n m`,
this is unconditional in the sense that it refers to no arbitrary
`m : MonodromyFunctional n`: the monodromy datum is the actual one. -/
noncomputable def actualRPAlpha (n : ℕ) : rpCohomology n 1 :=
  rpAlpha n (monodromyFunctional n)

/-- By definition, `actualRPAlpha n` is `rpAlpha n` of the actual monodromy
functional. -/
theorem actualRPAlpha_eq_rpAlpha (n : ℕ) :
    actualRPAlpha n = rpAlpha n (monodromyFunctional n) := rfl

/-- `actualRPAlpha n` agrees with the previously-introduced `rpAlphaW1 n`. -/
theorem actualRPAlpha_eq_rpAlphaW1 (n : ℕ) :
    actualRPAlpha n = rpAlphaW1 n := rfl

/-- The defining property of `actualRPAlpha n`: its Kronecker functional is the
`w₁` functional `w1Functional n`. -/
theorem actualRPAlpha_kroneckerMap (n : ℕ) :
    (kroneckerMap (TopCat.of (RP n)) 1).hom (actualRPAlpha n) = w1Functional n :=
  rpAlpha_kroneckerMap n (monodromyFunctional n)

/-- **Naturality / preservation of `actualRPAlpha`.** For every odd self-map `f`
of `Sⁿ` with descent `fbar = inducedOnRP f hf`, the pullback `fbar^*` fixes the
canonical class:

```text
(inducedOnRPPullback f hf 1) (actualRPAlpha n) = actualRPAlpha n.
```

This is the unconditional descended-odd-map invariance of the actual `α`,
specialising the conditional `inducedOnRPPullback_rpAlpha` to the genuine
monodromy functional. -/
theorem inducedOnRPPullback_actualRPAlpha {n : ℕ}
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    (inducedOnRPPullback f hf 1).hom (actualRPAlpha n) = actualRPAlpha n :=
  inducedOnRPPullback_rpAlpha n (monodromyFunctional n) f hf

/-- Alias of `inducedOnRPPullback_actualRPAlpha`, named for downstream use:
descended odd maps preserve the actual canonical class `α`. -/
theorem actualRPAlpha_preserved_by_inducedOnRP {n : ℕ}
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    (inducedOnRPPullback f hf 1).hom (actualRPAlpha n) = actualRPAlpha n :=
  inducedOnRPPullback_actualRPAlpha f hf

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
