# STW XXIX: projection-monoid dichotomy audit (2026-08-30)

## Exact reduction

For a simple real-rank-zero algebra, the finite/purely-infinite dichotomy is
equivalent to the following property of the projection monoid:

```text
nx properly infinite  implies  x properly infinite.
```

The reduction uses real rank zero only at the last step, to put a projection
in every nonzero hereditary subalgebra.  All propagation before that takes
place in `V(A)`.

## Propagation calculation

An infinite projection class has a nonzero defect `r` with `p+r=p`.
Simplicity gives `p<=kr`; hence

```text
2p <= p+kr=p,
```

so the infinite class is properly infinite.  For any nonzero projection
class `q`, choose `p<=lq` and `q<=mp`.  Then

```text
2lq <= 2lm p <= p <= lq,
```

so a finite multiple of `q` is properly infinite.  Projection-level QQ
makes `q` properly infinite.  Real rank zero then turns the projection
statement into pure infiniteness.

## New sufficient condition and counterexample fingerprint

If `V(A)` is unperforated, applying it to `n(2x)<=nx` proves projection-level
QQ.  Thus unperforated projection order is a sufficient condition for
Problem XXIX, with no nuclearity, stable rank, trace, or corona factorization
hypothesis.

Conversely, any mixed finite/infinite example contains a finite `q` with
`nq` properly infinite.  It therefore displays the concrete perforation

```text
n(2q)<=nq,             2q not <=q.
```

This sharpens the existing non-CFP requirement: a counterexample cannot
hide its irregularity only in multiplier projections or soft Cuntz classes;
it must already fail equal-multiple cancellation/order reflection in
`V(A)`.

## Boundary

Perera--Rordam weak divisibility for real-rank-zero algebras does not by
itself imply projection-level QQ.  Weak divisibility decomposes large
projection classes but does not reflect proper infiniteness from a finite
multiple.  The remaining monoid problem is therefore exact: determine
whether the simple refinement monoids arising as `V(A)` for real-rank-zero
algebras automatically have `(QQ_V)`, or construct one with the displayed
perforation while retaining C-star realizability and simplicity.
