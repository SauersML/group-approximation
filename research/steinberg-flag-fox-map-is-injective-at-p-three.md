---
rg: 2
id: steinberg-flag-fox-map-is-injective-at-p-three
kind: claim
title: The full Steinberg flag Fox map is injective in characteristic three
artifacts:
  - research/steinberg-p-three-full-fox-injectivity-proof.md
distinct_from:
  steinberg-zero-marginal-recurrence-is-zero-at-p-three: that assumes both panel marginals vanish; this proves the arbitrary-marginal recurrence and therefore the complete flag-map statement at p=3.
  steinberg-flag-fox-map-is-injective: that requires every odd prime; this establishes its first prime instance only.
---

**ESTABLISHED.**  Over `F_3`, every chord function satisfying both complete
Steinberg Fox recurrences `(SCA4)`, with all exceptional values interpreted
by `(STM2)`, is zero.  No zero-marginal hypothesis is needed.  Consequently
the characteristic-three flag-incidence Fox map is injective and its point
and plane marginals vanish automatically.

The proof begins with the exact one-scalar exceptional `Y` anchor, uses
`X,Y` to eliminate seven of the nine `(a,b)` fibers, reduces the eighth to
zero and the ninth to a constant, and kills that constant with one final
`A`-tree exception.

DERIVATION
steinberg-p-three-full-fox-injectivity-proof
