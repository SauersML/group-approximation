---
rg: 2
id: npa-nullity-upper-bound-via-triangular-shell
kind: route
title: Count five k minus three shell pivots plus two surviving old-class rows
target: npa-first-order-nullity-at-most-2k-plus-3
requires:
  - npa-shell-pivot-count-is-five-k-minus-three
  - npa-two-residual-rows-independent-mod-old-rows
  - npa-class-count-fixes-rank-nullity-dictionary
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

Order the moment classes by total degree.  The first prerequisite supplies, for
each of the `5k-3` non-exceptional new classes, a row of `Phi_k` in which that
class is the unique term of maximal degree and appears with coefficient `1`; over
the new classes these rows form a unit-triangular block, so they are independent
and stay independent modulo any set of rows supported on old classes.

The second prerequisite supplies two further rows, supported entirely on old
classes, that are independent modulo the level-`(k-1)` row space.  They cannot be
absorbed by the shell block either: a combination of shell rows with zero
new-class part is zero, by unit-triangularity.

Hence

```text
rank Phi_k  >=  rank Phi_(k-1) + (5k-3) + 2  =  rank Phi_(k-1) + 5k - 1,
```

and the third prerequisite converts that increment into `dim ker Phi_k <= 2k+3`
by rank-nullity against `C_k - C_(k-1) = 5k+1`, given the bound at `k-1`.

The route's honest weak point is inherited, not local: prerequisite two is where
the argument leaves proved ground.
