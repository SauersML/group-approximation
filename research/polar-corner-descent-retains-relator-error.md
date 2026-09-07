---
rg: 2
id: polar-corner-descent-retains-relator-error
kind: claim
title: Polar corner descent adds quadratic leakage but retains the original relator error
distinct_from:
  unitary-corner-compressions-force-reduction: that estimates leakage from a compression already close to a corner unitary in normalized Hilbert--Schmidt norm; this gives an operator-norm relator estimate after polar correction of an approximately invariant corner.
  canonical-swap-corners-have-no-dimension-descent: that computes the padding cost for one canonical arithmetic actor; this is a general estimate and an explicit two-dimensional obstruction for polar descent of group relations.
  property-t-free-manuscript-results: that asks for a complete alternative proof; this fences a proposed generic minimal-dimension descent and identifies the group-specific reconstruction it would need.
artifacts:
  - research/polar-corner-descent-retains-relator-error-proof.md
  - research/artifacts/property-t-free-compression-and-descent-check.py
---

**ESTABLISHED.** Let `U_1,...,U_k` be unitaries, let `P` be a projection,
and assume

```text
max_i ||[P,U_i]|| <= eta < 1.                           (PCD1)
```

For each signed generator, compress to `P C^d` and replace the compression by
its polar unitary. If a word `r` has length `ell`, then

```text
||r(V)-P||
 <= ||P(r(U)-I)P|| + ell(ell+1) eta^2/2.                (PCD2)
```

Consequently, if the original tuple satisfies a finite presentation with
operator-norm defect `delta`, the polar-compressed tuple has defect at most

```text
delta + ell(ell+1) eta^2/2                              (PCD3)
```

on relators of length at most `ell`. Approximate invariance contributes only
quadratic leakage, but ordinary corner descent does not contract the existing
relator error.

Even exact relations need not remain exact after polar descent: an explicit
two-dimensional tuple with `UV=W` acquires defect asymptotic to `eta^2` on a
rank-one corner. Therefore a Property-`(T)`-free infinite-descent proof would
need a group-specific reconstruction which cancels the inherited and leakage
errors; generic compression and polar correction do not supply it.

DERIVATION
polar-corner-descent-retains-relator-error-proof
