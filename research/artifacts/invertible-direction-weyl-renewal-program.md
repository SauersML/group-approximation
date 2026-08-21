# Sequential derivative resets as a finite selector-renewal backend

Former Cairn claim `invertible-direction-weyl-renewal-program`, demoted
because it records a completed local program and a remaining global caveat,
not one unresolved proposition.

Use one common invertible-direction baseline `A_k` for every predicate in a
fixed arity-`k` menu.  For each selector bit, the cell of
`weyl-derivative-reset-preserves-schur-spin-scale` replaces that bit by a
transverse commuting involution, makes the old bit private, and carries the
total baseline multiplicity through a fixed `2^N` spin packet. The implementer
is a fresh commuting chart coordinate, but a reverse group cell is still
required before it can be a coefficient in the next Schur baseline. Repeating
a completed forward/reverse cell at most `k` times would produce a finite
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

The two former local obligations are now closed.  Gauge doubling repairs the
semantic problem by translating two private shares while fixing their logical
product.  The affine selector Clifford construction puts all residual forms
in one finite type, makes the translation an ordinary commutator, and its
balanced four-point restriction restores the missing hyperbolic pair without
changing scale.  The route
`fresh-renewal-via-gauge-doubled-derived-reset` therefore establishes
`fresh-selector-renewal-after-symplectic-chart-reset`.

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
