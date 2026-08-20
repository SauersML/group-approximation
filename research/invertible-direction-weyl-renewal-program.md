---
rg: 2
id: invertible-direction-weyl-renewal-program
kind: claim
title: Sequential derivative resets are a candidate finite selector-renewal backend
distinct_from:
  fresh-selector-renewal-after-symplectic-chart-reset: that is the full Fanizza incidence theorem whose establishment would close the current goal; this records the newly solved algebraic cell and the one remaining compatibility audit without promoting the endpoint prematurely.
  finite-packet-cannot-realize-absorbing-contraction: that rules out deriving a complete contraction from one finite packet; this preserves only the scalar current and explicitly leaves its global contraction open.
---

Use one common invertible-direction baseline `A_k` for every predicate in a
fixed arity-`k` menu.  For each selector bit, the cell of
`weyl-derivative-reset-preserves-schur-spin-scale` replaces that bit by a
transverse commuting involution, makes the old bit private, and carries the
total baseline multiplicity through a fixed `2^N` spin packet.  Reversing a
second copy of the same cell installs the new bit as the central selector of
the next baseline packet.  Repeating this at most `k` times produces a finite
zig-zag

```text
A_old -- L_1 -- A_1 -- L_2 -- ... -- L_k -- A_new.       (IWR1)
```

Every edge in `(IWR1)` identifies isomorphic finite packet groups.  Old and
new selector copies are not jointly centralized: each replaced pair obeys a
Weyl commutator with phase `J`.  Total multiplicity remains measured in units
of the same `2^N` spin dimension at every vertex.  Since `k` and the predicate
menu are fixed, finite-group exactification gives a computable
`O(sqrt(E))` loss and the number of relator occurrences is bounded.

This removes two former algebraic defects at once:

1. the reset no longer globalizes past selector centers; and
2. the endpoint no longer fuses the Schur current by restricting to a smaller
   spin packet.

It is not yet credited as `fresh-selector-renewal-after-symplectic-chart-reset`.
One compatibility check remains: in the actual Fanizza incidence, the
context-local corrected selectors are compared to the original shared BCS
words before and after `(IWR1)`.  The reverse cells must preserve those
fixed-word comparison estimates without identifying a shared original
variable with both members of a transverse Weyl pair.  This is a bounded
finite incidence audit for the three factored predicate shapes, but it is
semantically essential.  Passing that audit would establish the fresh-reset
hole; failing it would locate the obstruction in the original-word overlap,
not in affine rank or packet multiplicity.

The global scalar return is separate.  A finite zig-zag has a regular
stationary flow, so the one remaining scalar current must still be placed in
the one-sided Fanizza/Toeplitz recurrence or another finite-dimensional-only
holonomy.  No contraction is claimed here.

## Attempts

- The local affine-rank and packet-scale problems are resolved by the
  invertible-direction pencil and the two-copy Weyl derivative cell.
- The obvious finite zig-zag endpoint fails as a global return: its negative
  regular summand supplies an exact stationary multiplicity flow.  The attack
  is therefore deferred to the bounded shared-word audit followed by a
  one-sided, finite-dimensional-only Toeplitz/Fanizza placement.
