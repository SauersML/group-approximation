---
rg: 2
id: odd-maslov-llp-via-faithful-non-equivariant-retract
kind: route
title: Transfer even-fibre LLP through a faithful non-equivariant ucp retract
target: sp4-mod3-twisted-fibres-have-llp
requires:
  - sp2g-z-full-c-star-algebra-has-llp
  - metaplectic-half-class-has-an-exact-finite-model
---

**INVALIDATED ROUTE.**  The proposed relaxation of equivariant Morita
transport was to find split ucp maps

```text
A_(1/3) -> M_n(A_0 or A_(1/2)) -> A_(1/3)
```

whose retraction is faithful (in particular, a faithful conditional-
expectation or faithful-corner construction), while allowing the first map
to mix canonical generators non-equivariantly.  LLP of the even fibre would
then pass through the matrix amplification and ucp retract.

`odd-maslov-ucp-retract-must-hide-generator-defect` refutes this mechanism.
Schwarz forces every left and right multiplicative defect of every canonical
generator image to be a positive element killed by the retraction.  If the
retraction is faithful, all defects vanish; the embedding becomes a
star-homomorphism by the multiplicative-domain theorem.  Composing with a
finite-dimensional representation of the untwisted or metaplectic target
then produces a forbidden finite-dimensional odd-Maslov representation.

The target claim remains open only for a genuinely nonfaithful ucp retract
whose positive kernel absorbs nonzero generator defects, or for a proof not
based on such a retract.
