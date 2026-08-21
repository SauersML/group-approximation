---
rg: 2
id: canonical-selected-type-carrier-dichotomy
kind: route
title: Reduce canonical Fanizza type alignment to algebraic corner transport or a matrix-only common-carrier theorem
target: fanizza-canonical-profile-groupification
requires:
  - finite-product-selected-type-mark-does-not-align-carriers
  - canonical-full-type-overlap-is-algebraic-corner-containment
  - selector-edge-type-support-is-twist-invariant
  - all-bcs-contexts-share-one-hyperoctahedral-signed-type
  - tracial-bcs-rationalizes-full-overlap-distributions
---

Canonical-delta microstates restrict to the regular character on every fixed
finite packet.  Thus every rational primitive packet idempotent `q_c` has its
correct positive Plancherel mass, and noncanonical forbidden-sector
representations are irrelevant.  The remaining alignment problem has the
following sharp dichotomy.

### Algebraic lane

Construct a rational group-algebra projection `q` and finite-support corner
partial isometries which transport every local selected packet carrier onto
`q`, intertwine every complete overlap distribution, and let at least one
context block escape the finite root algebra.  By
`canonical-full-type-overlap-is-algebraic-corner-containment`, full canonical
overlap is exactly this algebraic containment statement.  The normalized
local ranks and overlap distributions are already supplied by the two last
requirements above.  The remaining object is precisely the block-escaping
signed-Hecke holonomy, not another finite-type normalization.

The edge cannot be selector-free.  By
`selector-edge-type-support-is-twist-invariant`, the `C17` edge must retain
all three logical selector directions, while `C13/C14` and `C18` require
ranks two and four respectively.  Gauge doubling changes no one of these
logical rank lower bounds.  The holonomy must carry this data without
identifying the noncommuting selector algebras around the native incidence
cycle.

### Matrix-only lane

Prove directly that survival of the canonical group-algebra mark forces a
positive-density common reducing carrier, with enough shared-variable
intertwining to invoke Fanizza soundness.  A finite product of local type
projections is not such a certificate:
`finite-product-selected-type-mark-does-not-align-carriers` gives canonical
dihedral microstates where the product norm stays `1/2` and the common
carrier density tends to zero.  Therefore this lane needs an additional
source-specific mixed-moment or overlap-to-reducing-corner theorem.

### HALT completeness

The algebraic lane is compatible with an exact properly infinite witness.
Start from the HALT BCS GNS representation, gauge-covariantize it, amplify
countably, and realize the finitely many equal-rank packet transports by
Hilbert-hotel unitaries.  No global finite trace is required.  The mark may
be the rational corner signal `qD_m`, so no group word has to return the
selected type.

### What is retired

The following intermediate claims are insufficient even under canonical
trace conditioning:

```text
all local q_c have the same positive trace;
all pairwise cross-Gram operators are nonzero;
a finite product q_m u_(m-1)...u_1 q_1 survives;
the reset edge carries only a common selector-free spin type.
```

The exact live endpoint is either a finite-support block-escaping corner
transport satisfying the full overlap identities, or a new matrix-coordinate
theorem which upgrades partial overlap to a common reducing carrier.  This
route makes the choice explicit and removes the product-mark and
selector-free reset ambiguities from `fanizza-canonical-profile-groupification`.
