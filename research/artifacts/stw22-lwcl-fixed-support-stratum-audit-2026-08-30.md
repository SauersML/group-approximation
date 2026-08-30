# STW XXII: local weighted lifting on fixed support strata

## What the strong-topology bundle theorem supplies

For the hyperfinite `II_1` factor, projections of one fixed trace form a
strong-topology orbit.  Andruchow--Varela Theorem 2.10 gives the continuous
section of the modular-state fibration, while their Theorem 7.2 continuously
assigns to a projection `q` its normalized corner trace `tau_q`.  Their
composition supplies a continuous partial isometry from one fixed initial
projection onto `q`.  Therefore a `2`-norm-continuous projection field of
locally constant trace can be locally lifted from one fixed initial
projection.

Multiplying such a lift by the square root of the positive field gives an
exact local weighted corner embedding.  This proves `(LWCL)` on a fixed
support stratum.

Primary reference: E. Andruchow and A. Varela,
[*States with equivalent supports*](https://jot.theta.ro/jot/archive/2005-053-001/2005-053-001-002.pdf),
Journal of Operator Theory 53 (2005), 35--48.

## What it does not supply

An `L^2`-continuous positive field can acquire large new support carrying
arbitrarily small eigenvalues.  Its support projection can therefore jump
or change trace even though the weighted field is continuous.  Such a field
does not remain in one projection orbit, so the fixed-support bundle theorem
cannot be invoked.

Sequential lower lifting controls weighted operators across those jumps and
is enough on a zero-dimensional base via clopen approximation.  It does not
automatically give a parametrized local section on a positive-dimensional
neighbourhood.  The cross-stratum local selection problem, not the topology
inside a fixed projection orbit, is the remaining LWCL hinge.
