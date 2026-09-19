# Selector-flip covariance splits off from the native Fanizza triangle

Let `B` be the finite native triangle packet after gauge doubling, and let
`K` be its elementary abelian group of incidence selector flips.  Each
`k in K` acts by an automorphism `theta_k` of `B`, and every logical
observable and prescribed logical word is fixed by every `theta_k`.

Start with any finite-dimensional representation `pi` of the local packet.
The standard covariantization is

```text
Pi(b)=direct_sum_(g in K) pi(theta_g(b)),
S_k(delta_g tensor xi)=delta_(kg) tensor xi.            (SFS1)
```

Then

```text
S_k Pi(b) S_k^*=Pi(theta_k(b)).                         (SFS2)
```

For every logical word `x`, `theta_k(x)=x`, so

```text
[S_k,Pi(x)]=0.                                          (SFS3)
```

Thus selector implementation is a split finite spectator symmetry on the
entire logical/machine-word algebra.  It cannot by covariance alone create
a proper-corner loss there.

Start with the exact `S_4` stationary-overlap model from
`fanizza-reflection-recurrence-has-s4-stationary-overlap` and adjoin an
independent commuting sign for any separator not already present.  The three
triangle separators commute.  Decompose their joint finite spectrum.
`flat-fanizza-triangle-realizes-every-separator-distribution` says that every
one of the eight characters extends to all private context variables.
Choose such an extension on each joint eigenspace (after a common finite
amplification if necessary).  This installs the flat native triangle without
changing the `S_4` prescribed-word recurrence on the shared separators.

Gauge-double this combined finite packet and apply `(SFS1)`.  Finally tensor
it with an independent finite D8 packet having the canonical mixture

```text
tr(H)=1/8,       H=(1-[R_F,R_G])/2.                     (SFS4)
```

All native triangle relations, all selector-flip covariance relations, and
the ordinary reflection recurrence therefore hold exactly on one model.
The selector unitaries
act only on the gauge-orbit factor, and the D8 packet remains independent.
Therefore these ingredients cannot imply either proper return in `(STR1')`,
much less `(STR1)`: finite-dimensional cyclicity would otherwise force
`(SFS4)` to vanish in this exact model.

This does not model the full nonlinear guarded C18 machine-word semantics.
That is exactly the boundary.  A remaining cell must add a mixed word
`r(S,x)` which couples a selector implementer to the nonlinear prescribed
machine-word multiplicity, forces the finite-dimensional loss of the `H`
carrier, and still has a one-sided countably amplified HALT realization.
The word cannot be mere covariance on the logical fixed algebra, because
`(SFS3)` makes that split.  Nor can it use only the reflection recurrence,
because the `S_4` factor realizes that recurrence with stationary overlap.

This is a sharp multiplicity-gauge countermodel, not a refutation of
`single-triangle-trace-cyclic-return-cell`: that claim explicitly permits
such a new finite-matrix-only mixed two-cell.
