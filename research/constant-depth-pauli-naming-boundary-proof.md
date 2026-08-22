---
rg: 2
id: constant-depth-pauli-naming-boundary-proof
kind: proof_route
target: constant-depth-pauli-naming-does-not-create-schur-contraction
uses:
  - schur-child-toeplitz-morita-wire
  - finite-packet-cannot-realize-absorbing-contraction
---

Because `m` is fixed, adjoin all rows `(CDP1)` and exactify their union as
one finite packet.  Realize the same finite data on properly infinite
multiplicity factors to verify exact marked completeness.  This proves the
positive localization statement.

For the boundary, inspect `(STM2)--(STM3)`: the two child charts recover
`M_2 tensor End(M)`, so their unweighted union preserves the full doubled
multiplicity rather than choosing a smaller return.  Any contraction deduced
only from the fixed packet table would hold on the negative regular summand,
where `finite-packet-cannot-realize-absorbing-contraction` gives an immediate
contradiction.  Therefore a joint ambient one-sided payment relation remains
necessary.
