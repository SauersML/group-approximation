---
rg: 2
id: purely-infinite-unit-group-max-mf-quotient-is-k1
kind: claim
title: The maximal MF quotient of the unit group of a purely infinite simple ring is its algebraic K1
distinct_from:
  properly-infinite-unit-group-is-not-mf: that says the unit group is not MF under the weaker full-idempotent hypothesis; this computes its maximal MF quotient exactly under pure infiniteness and simplicity, and the earlier claim is the statement that this quotient is proper.
  full-defect-ring-non-mf-at-rank-two: that is total collapse for the elementary groups under a weaker ring hypothesis; this is a classification for the whole unit group, where the collapse is total exactly when K_1 vanishes.
  agp-purely-infinite-simple-k1-is-unit-abelianization: that identifies K_1 with the unit-group abelianization, an algebraic fact with no approximation content; this identifies the same group as the maximal MF quotient.
artifacts:
  - research/artifacts/canonical-k1-mf-quotient-proof.md
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsKappaProof.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientCanonicalKOne.lean
  - research/artifacts/k1-classification-and-extension-bridge-2026-09-07.md
  - non_mf_groups_exist.tex
---

Let `R` be a countable unital purely infinite simple ring.  Every
homomorphism from `R^x` to an MF group factors uniquely through

```text
kappa : R^x --> K_1(R),
```

and `ker kappa = [R^x, R^x]` itself has full MF radical.  So

```text
Rad_MF(R^x) = [R^x, R^x],       R^x / Rad_MF(R^x) = K_1(R).
```

The maximal MF quotient of the unit group is exactly the algebraic `K_1` of
the ring.  In particular `R^x` has full MF radical if and only if
`K_1(R) = 0`.

Consistency: `K_1(L_(F_2)(1,2)) = 0` recovers the total collapse recorded in
`binary-leavitt-all-ranks-full-mf-radical`.

## Direct higher-rank proof

`purely-infinite-matrix-mf-quotient` proves the exact elementary/commutator
MF kernel, its intrinsic full radical, and unique factorization through
abelianization for every GL_n(R), n >= 2, without the AGP inputs. Its Lean
endpoint is `MFQuotientMatrices.manuscriptMFQuotientMatrices`. This is a
separate proof of that scope, with the elementary-group identification and
intrinsic full radical proved at every rank at least two.

`supported-unit-commutators-lie-in-corner-units` supplies the supported-unit
step as `MFQuotientUnits.agpStepOne`. Together with the abstract
abelianization package and the explicit Peirce reduction in
`purely-infinite-all-rank-mf-quotient`, it closes the all-rank group-theoretic
endpoint `MFQuotientUnits.manuscriptMFQuotientUnits`, including rank one.
There are no AGP input propositions in that endpoint.

`purely-infinite-canonical-k1-all-ranks` now closes the canonical gap:
`MFQuotientUnitsKOne.agpUnitKappa` identifies the constructed algebraic K1,
and `manuscriptCanonicalKOne` gives the actual canonical quotient map,
unique factorization, and intrinsic full radical of its kernel at every
positive rank. The existing printed base-ring endpoint is discharged as
`manuscriptMFQuotientUnitsKOneAtBaseRing`. This route uses no AGP citation
or general Morita input proposition. The separate general `MoritaKOne`
interface, which quantifies over all rings, is outside its scope.
