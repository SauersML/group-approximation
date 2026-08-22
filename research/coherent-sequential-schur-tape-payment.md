---
rg: 2
id: coherent-sequential-schur-tape-payment
kind: claim
title: Compose the uniformly rounded Clifford cells and charge every inactive selector sector
distinct_from:
  uniform-relative-clifford-tape-cell: that asks for depth-independent rounding of one new cell conditional on an exact old prefix; this uses the sufficient polynomial-cost Toeplitz coordinate-Pauli replacement, composes the cells, and proves the scalar contraction recurrence.
  non-ce-bcs-has-robust-approximate-energy-gap: that converts marked contextuality into total forbidden-product mass; this routes that mass through the oriented tower restriction matrices.
---

Polynomial-cost one-step relative exactification along the self-referential BCS tape
admits normalized marked multiplicities `a_n` such that:

1. the base signal gives `(SDL1)`;
2. every selector sector activating the Schur rank jump contributes the
   factor `1/2` from the restriction matrix;
3. every inactive sector is charged to the corresponding BCS violation mass,
   and the Fanizza signal-collapse/decomposition estimate charges its total
   contribution by `K(n+1)^k sqrt(E)`;
4. discarded overlap corners are bounded using
   `shared-overlap-controls-packet-multiplicity-vector` with the same
   polynomially weighted cost.

Then `(SDL2)` holds uniformly in the tape level.

## Attempts

- **Greedy sequential polar alignment.** Pairwise overlap loses only
  `O(delta_n^2 d)` dimensions, so the geometrically weighted sum is harmless
  if `delta_n` grows polynomially. The unresolved point is that the next
  relative exactification is performed on the surviving residual factor; a
  discarded selector corner can re-enter through a different context unless
  the corrections are chosen monotonically.
- **Type-vector formulation.** Avoid nested subspaces and track only the full
  weighted irreducible multiplicity vector at each level. Pairwise alignment
  bounds its discrepancy. This is now the successful proof: orient the Schur
  predicate to be one on propagation-satisfying sectors and apply
  `oriented-schur-restriction-mass-identity`. The complementary coordinate is
  exactly inactive/forbidden mass and `(FDB2)` charges it. Since complete type
  vectors, rather than retained corners, are compared at every incidence,
  there is no uncharged re-entry channel.
