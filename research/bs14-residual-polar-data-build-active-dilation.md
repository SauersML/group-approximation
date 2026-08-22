---
rg: 2
id: bs14-residual-polar-data-build-active-dilation
kind: claim
title: Two cubic residual polar data build the active flexible dilation
distinct_from:
  bs14-flexible-cross-packet-boundary-reconciliation: that asks for the sharp global semigroup repair; this asks only for the weaker active/passive dilation sufficient for qualitative flexible stability.
  bs14-energy-threshold-active-passive-ledger: that starts from a known positive corner; this must construct the corner directly from a near-solution.
  bs14-residual-invariant-hull-has-unbounded-packet-loss: that rules out invariant hulling; this requires a non-invariant joint Gram completion instead.
---

OPEN.  Let `(R,S)` be an exact finite-dimensional `BS(1,4)` core and let
`X` have normalized four-relator energy `e`.  Put

```text
D_1=(XS^2)^3-1,              D_2=(XRS)^3-1,
tau=e^(1/4),                 theta=c tau,             (RPD1)
```

and form the high singular spectral subspaces of `|D_1|,|D_2|` above
`theta`, together with their polar partial isometries and mutual principal-
angle decomposition.

Construct from these data, without an assumed ambient dilation:

1. at most `C e^(1/2)d` new trivial-BS dimensions;
2. a joint source/exit Gram completion coupling those dimensions to the
   original space;
3. an exact Iwahori tuple on the enlarged space;

so that its compression is within `O(e^(1/8))` normalized HS of the input
tuple.

## Attempts

- `bs14-energy-threshold-active-passive-ledger` proves exactly these rates
  when the input is already known to be a polar compression of a positive
  fixed corner.
- Transverse high-residual carriers recover the source by
  `two-cubic-residual-carriers-recover-the-deleted-source`; nearly parallel
  carriers are handled by the active/passive energy dichotomy, so a uniform
  angle is unnecessary.
- `bs14-residual-invariant-hull-has-unbounded-packet-loss` rules out the
  obvious construction: the BS-invariant hull of one rank-one source can be
  an entire unbounded packet.  The new dimensions must carry the trivial BS
  type and couple non-invariantly through one joint Gram completion.
- The remaining exact obstruction is integral rather than spectral: the two
  residual polar decompositions must be rounded to one common collection of
  source/exit cells with integer multiplicities.  Separate singular-value
  rounding of `D_1,D_2` does not ensure their cells use the same added
  dimensions or satisfy both cubic equations.
