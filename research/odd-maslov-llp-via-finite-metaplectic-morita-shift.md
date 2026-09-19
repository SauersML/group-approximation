---
rg: 2
id: odd-maslov-llp-via-finite-metaplectic-morita-shift
kind: route
title: Transport base LLP to the odd Maslov fibre using the exact metaplectic finite model
target: sp4-mod3-twisted-fibres-have-llp
requires:
  - sp2g-z-full-c-star-algebra-has-llp
  - metaplectic-half-class-has-an-exact-finite-model
---

**INVALIDATED ROUTE.**  The proposal was to imitate the established
metaplectic half-shift: tensor the untwisted or half-twisted generators by
finite quotient representations of the residually finite metaplectic base,
place the odd `1/3` or `1/6` generators in a finite matrix amplification, and
compress an invariant conjugate pair to obtain a ucp retraction.  LLP would
then pass from the base fibre to the odd fibre.

This cannot work.  By
`finite-metaplectic-morita-shifts-cannot-reach-odd-maslov-fibres`, every such
finite generator-equivariant tensor/Morita bridge carries an exact projective
coefficient whose multiplier is the difference of the source and target
twists.  Reaching the odd orbit therefore requires an exact finite
`1/3`, `2/3`, `1/6`, or `5/6` coefficient.  Deligne finite-dimensional
invisibility forbids all four.  Finite representations coming from `E_2`
generate only the classes `0` and `1/2`, so amplification and repeated
metaplectic shifts never escape the already established half-shift orbit.

The invalidation is scoped to this finite equivariant Morita/retract
mechanism.  It does not refute the target LLP claim or a genuinely
non-equivariant ucp construction.
