# Audit: finite-base upper-semicontinuous fibre product bound

Date: 2026-08-30

Claim: `stw81-finite-base-usc-fibre-product-bound`.

## Checks

1. The proof uses only upper semicontinuity of fibre norms.  Exact outgoing
   lifts come from projectivity of finite-dimensional cones; no local lift
   of the incoming c.p.c. map is asserted.

2. The topological refinement supplies `n+1` families with disjoint closed
   supports inside the anchor neighborhoods.  Pairing these with the `d+1`
   fibre colours gives exactly `(n+1)(d+1)` order-zero summands.

3. Multiplication by a positive central cutoff preserves order zero.
   Disjointness within each base colour makes the direct sum order zero even
   though different base colours can overlap.

4. The separately lifted fibre colours need not sum contractively away from
   their anchor, and no such condition is part of nuclear dimension.  Each
   paired `(base colour,fibre colour)` return is individually c.p.c. order
   zero because its coordinate supports are orthogonal.  No common scaling
   is used.

5. The approximation estimate is a convex partition-of-unity estimate, so
   it does not acquire a factor equal to the number of cover sets or
   colours.

6. For simple fibres, a commutative hereditary fibre is zero unless the
   ambient simple fibre is elementary, and then it has rank at most one.
   The spectrum map is injective.  Compact-neighborhood embeddings into
   `X`, rather than an unproved global properness assertion, give the shadow
   dimension bound.

## Boundary

The product estimate is not asserted to be sharp for positive-dimensional
bases.  In particular, over a one-dimensional base with fibre dimension
one it gives nuclear dimension at most three, not the trichotomy demanded
by Problem LXXXI.

Outcome after removing the unnecessary total-contractivity step: **PASS**.
