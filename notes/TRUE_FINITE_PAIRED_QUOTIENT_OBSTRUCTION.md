# The finite paired-radical endpoint is now kernel-checked

Date: 2026-08-13

## Outcome

The algebraic endpoint of the paired-radical-quotient program no longer
depends on a dimension count left in prose.  It has a basis-free finite-set
form which uses only point separation, two diagonal transport identities,
and one crossed-zero identity.

Let `V,W` be finite sets, let `B(v,w)` be a relation which separates points
in both variables, and suppose

```text
B(R0 v,L0 w) <-> B(v,w),
B(R1 v,L1 w) <-> B(v,w),
not B(R0 v,L1 w).                                  (FPQ1)
```

Then `B` is empty.  Indeed, the first diagonal identity and left separation
make `R0` injective, while the second diagonal identity and right separation
make `L1` injective.  Finiteness makes both maps surjective.  Every pair
`(v,w)` is therefore `(R0 v0,L1 w1)`, and the crossed identity in `(FPQ1)`
annihilates it.

The theorem is formalized in
`GroupApproximation/Leavitt/FinitePairedQuotientObstruction.lean` as

```text
no_finite_nonempty_separating_pairing_with_leavitt_transports
```

It was checked on MSI against the existing warm Lean build.

## Application to the binary Leavitt pairing

For an additive functional `ell : R -> F2`, put

```text
b_ell(a,b) = ell(a b).
```

After quotienting the two variables by the left and right radicals, the
induced pairing separates points.  Right multiplication by `t_i` and left
multiplication by `s_j` satisfy

```text
b_ell(a t_i,s_j b) = delta_ij b_ell(a,b).           (FPQ2)
```

Thus `(FPQ1)` is precisely the `00`, `11`, and `01` part of `(FPQ2)`.  No
finite nonzero paired radical quotient can carry these transports.

## Exact scope

This closes the finite algebraic endpoint; it does **not** solve the
hyperlinear problem.  A normalized-Hilbert--Schmidt microstate does not
automatically provide the two finite radical quotients, a flat Fourier
pairing between them, or transport maps on common multiplicity spaces.
Constructing those objects with dimension-independent error is still the
live analytic gate.

The formal theorem is useful because it specifies the minimum successful
extraction.  Full recovery of the coefficient ring is unnecessary.  It is
enough to recover:

1. two finite point-separating coefficient quotients;
2. the diagonal transports `R0/L0` and `R1/L1`; and
3. the single crossed-zero transport `R0/L1`.

Once those data are available, there is no remaining algebraic or
finite-dimensional argument to invent.
