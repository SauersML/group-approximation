# The two raw branches form an exact Pauli transfer packet

Date: 2026-08-13

## Outcome

The two branch operators left implicit in
`TRUE_RAW_BRANCH_PAULI_CELL.md` have an exact basis-free formula.  Work on the
central sector where the raw/cylinder commutator is `-1` and the independent
`z_001` sign is `-1`.  Let

```text
P = negative cut of z_11,
Q = joint carrier cut (commutator = -1 and z_001 = -1),
R = raw involution,
U = comb unitary.
```

On this carrier, `P` and `Q` commute, `R` preserves `Q`, and `R` flips the two
`P` halves:

```text
R P R = 1 - P.
```

Define

```text
E  = P Q,
T0 = U* P Q,
T1 = U* R P Q.                                      (PBT1)
```

Then both arrows have initial projection `E`, their range projections are
orthogonal, and their sum is exactly the transported larger carrier:

```text
T0* T0 = E,
T1* T1 = E,

(T0 T0*) (T1 T1*) = 0,
T0 T0* + T1 T1* = U* Q U.                           (PBT2)
```

These identities use only finite-dimensional Pauli algebra.  They are now
kernel-checked in `GroupApproximation/Sofic/PauliBranchTransfer.lean`.

## Trace accounting

In the regular finite packet already audited,

```text
tau(Q) = 1/4,
tau(E) = 1/8.
```

Thus `(PBT2)` is exactly trace-balanced:

```text
tau(T0 T0*) + tau(T1 T1*) = 1/8 + 1/8 = 1/4.
```

The two arrows are genuine isometric copies of the trace-`1/8` initial
space, but they fill a trace-`1/4` carrier.  This is why the Pauli cell by
itself is realized in a finite matrix algebra.

Only one additional assertion would finish the atlas route:

```text
U* Q U <= E.                                         (PBT3)
```

Indeed `(PBT2)` and `(PBT3)` would place two orthogonal trace-`1/8` ranges
under a trace-`1/8` projection.  Equivalently, taking traces would give
`1/4 <= 1/8`.

At a finite matrix coordinate this does not require an analytic estimate:
the ranks are `d/4` and `d/8`, and

```text
(1-E)F=0  implies  F=EF  implies  rank(F)<=rank(E).
```

`one_sub_mul_ne_zero_of_rank_lt` kernel-checks this terminal dimension
argument.  Quantitatively, for orthogonal projections the squared normalized
Hilbert--Schmidt leakage satisfies

```text
||(1-E)F||_2^2 >= tau(F)-tau(E)=1/8.                  (PBT4)
```

Thus an approximate version of `(PBT3)` has a fixed gap; vanishing-density
leakage is no longer available once the trace-`1/4` carrier has been
identified.

So the entire two-child obstruction is now one support-containment statement,
not four unknown contraction operators and not a reconstruction of a full
Leavitt family.

## Why the coefficient identity does not prove `(PBT3)`

This audit exposes a precise category error which must not be hidden in the
last step.

In the characteristic-two coefficient ring, a child idempotent `f` below a
parent idempotent `e` satisfies

```text
e f = f.
```

In an additive root character `ell`, the Steinberg commutator records only

```text
ell(e f) = ell(f).
```

It does **not** say

```text
ell(f)=1  implies  ell(e)=1.
```

For two linearly independent idempotents `e` and `f` with `ef=f`, there is
an additive functional with `ell(e)=0` and `ell(f)=1`.  Hence the negative
spectral projection of the root sign for `f` need not lie under the negative
spectral projection for `e`.  The regular representation of the finite root
subgroup realizes exactly these independent signs.

This is not a small error term.  It is an exact obstruction to every proof
which replaces coefficient idempotents directly by negative additive-root
cuts.  The star synchronizer does not change it: star supplies adjoints, while
the failed implication is multiplication-to-module-support.

## The exact remaining theorem

To prove `(PBT3)`, the matrix model must contain more structure than a point
of the additive character space.  It must recover a finite module on which
multiplication by the parent acts as the identity on the child range.  The
pair-of-radical-quotients formulation is precisely this extra structure:

```text
b_ell(a,b) = ell(ab),
V_ell = R / leftRad(b_ell),
W_ell = R / rightRad(b_ell).
```

On these quotients, `ef=f` becomes an actual operator identity, and therefore
can become support containment.  The live gate is consequently:

> recover a positive-density finite approximation of the paired radical
> quotients from the synchronized raw-compressor microstate, and identify its
> transported `Q` carrier with the Pauli coefficient carrier `E`.

This is narrower than generic commutant recovery but stronger than root
Fourier exactification.  Any successful proof must name the raw-compressor or
cross-chart relation which resolves the extension fibers; cross-root
commutator signs alone cannot do it.

## Formal certificate

`PauliBranchTransfer.lean` proves:

- the common initial cut is a projection;
- both transported arrows have that same initial projection;
- their named ranges are exactly `T_i T_i*`;
- the raw conjugate is the complementary half inside `Q`;
- the two ranges are orthogonal;
- their sum is `U* Q U`.

The file passes Lean on the existing warm MSI build.  No local code or build
was run.
