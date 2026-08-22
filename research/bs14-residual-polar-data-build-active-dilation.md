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

Construct from these data, without an assumed ambient dilation, a split in
which the `R`-fixed active source part is dilated and the orthogonal active
part is corrected internally or discarded:

1. prove that the high-residual source component orthogonal to `Fix(R)` can
   be removed or internally corrected at `O(e^(1/8))` normalized-HS cost,
   without taking its possibly unbounded BS-invariant hull;
2. add at most `C e^(1/2)d` new trivial-BS dimensions for the remaining
   `R`-fixed source component;
3. build a joint source/two-exit Gram completion and an exact Iwahori tuple
   on the enlarged space;

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
- **Inversion adds a typed linear constraint before network-flow
  integrality.**  `bs14-trivial-boundary-inversion-forces-r-fixed-source`
  proves that the neutral added dimensions are forced to carry the trivial
  BS character and every source map must satisfy

  ```text
  RB=B,                 AR=R^(-1)A.
  ```

  Thus an untyped CS cell whose source is not `R`-fixed cannot be repaired by
  adding one trivial line, regardless of integer rounding.  On a scalar
  packet this forces return phase `v=1` and selects its unique `R`-fixed
  orbit sum.  The remaining transportation problem is therefore over these
  typed fixed-source cells, together with the involution Gram equations
  `(TBI3)`, not over arbitrary carrier dimensions.
- The phrase "add trivial-BS dimensions" cannot cover a `v!=1` active
  source: `(TBI2)` makes its coupling block exactly zero.  The earlier
  formulation silently treated every high-residual carrier as dilatable and
  was therefore too strong at the cell level.  The statement above now
  separates the missing phase-off-one internal correction/discard estimate
  from the `v=1` dilation.
- Even on the fixed-source sector, this is not an ordinary bipartite
  transportation problem.  `bs14-two-exit-typed-transport-is-not-saturated`
  writes the necessary matrix as a three-partite three-uniform incidence
  matrix and exhibits a determinant-two, index-two hole.  It remains to
  prove native-support balancedness, pay such parity holes within the active
  ledger, or use the operator Gram equations to exclude them.
- `bs14-native-cell-padding-preserves-lattice-charge` shows that the phrase
  "pay such a hole by padding" must permit a controlled **change of cell
  type**.  Same-support padding preserves the incidence-lattice coset, so
  the determinant-two example cannot be repaired by adjoining any number of
  its four native cells, even though doubling the whole margin vector
  integralizes it.  The remaining statement must authenticate
  support-enlarging cells (or perturb the rounded margins); a bounded
  saturation exponent alone is logically insufficient.
