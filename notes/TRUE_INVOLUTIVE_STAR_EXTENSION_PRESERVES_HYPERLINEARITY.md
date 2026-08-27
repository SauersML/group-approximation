# The involutive star extension preserves hyperlinearity

Date: 2026-08-13

## Outcome

The finite extension used to spatialize the Leavitt star operation introduces
no new hyperlinearity hypothesis.  If `Q` is a group and
`psi in Aut(Q)` satisfies `psi^2=1`, then

```text
Qsharp = Q semidirect_psi C2
```

is hyperlinear if and only if `Q` is hyperlinear.

The reverse implication is restriction to the subgroup `Q`.  The forward
implication has an explicit two-sheet matrix proof.  Consequently we may add
the star synchronizer to the atlas candidate, use its exact conjugation
relations, and still be attacking the original hyperlinearity question rather
than a stronger problem about a new group.

## The two-sheet construction

Let `U_q` be a finite unitary microstate for `Q`.  On two copies of its
matrix space define

```text
D(q) = diag(U_q, U_(psi(q))),
J    = [ 0  I ]
       [ I  0 ].
```

Then the exact block identities are

```text
J^2 = I,
J D(q) J = D(psi(q)),
D(q) D(r) = diag(U_q U_r, U_(psi(q)) U_(psi(r))).
```

Thus, for `epsilon in C2`, the assignment

```text
R(q,epsilon) = D(q) J^epsilon
```

has precisely the multiplication law of `Q semidirect_psi C2`, up to only
the original multiplicativity errors of `U`.

For a prescribed finite set in the semidirect product, request the original
`Q`-microstate on the finite set containing both coordinate projections and
their `psi`-images, together with the finitely many products occurring in the
semidirect multiplication table.  There is no uniformity or diagonal-choice
issue: this is one finite enlargement of the requested window.

## Metric audit

The normalized Hilbert--Schmidt error in a diagonal double is the average of
the errors on its two sheets:

```text
d_HS(D(A,B), D(C,D))^2
  = (d_HS(A,C)^2 + d_HS(B,D)^2) / 2.
```

Right multiplication by `J` is unitary, so the same formula controls the odd
sheet.  Therefore multiplicative error remains at most the original error.

Separation has two cases.

1. On the same `C2` sheet, separation is the average of the separations of
   `(q,r)` and `(psi(q),psi(r))`.  Since `psi` is injective, both pairs are
   distinct whenever `q != r`.
2. On different sheets, one relative product is off diagonal.  Its normalized
   trace is exactly zero, so two unitaries have squared normalized
   Hilbert--Schmidt distance exactly `2`, the maximal target separation in the
   repository's definition.

This proves hyperlinearity of the semidirect product directly from the finite
microstate definition.  Conversely, `Q` embeds as the even sheet, and
hyperlinearity passes to subgroups.

The same two-sheet argument proves the corresponding sofic finite-extension
closure with permutations in place of unitaries.  For the present application
only the contrapositive subgroup direction is needed: if `Q` is nonsofic, then
`Qsharp` is nonsofic.

## Application to the synchronized Leavitt atlas

In `TRUE_RAW_STAR_SYNCHRONIZED_SECTOR.md`, the operation on the finite
compressed chart is

```text
psi(g) = theta(g^(-1)),
```

and is involutive.  Adjoining its order-two implementer makes the Leavitt star
an honest conjugation operation.  The calculation above now certifies that
this modification is logically free for the target problem:

```text
Q is hyperlinear       iff Qsharp is hyperlinear,
Q is nonsofic          implies Qsharp is nonsofic.
```

This closes the star/adjoint compatibility gate.  It does **not** close the
remaining atlas gate.  The first hard branch elements still do not lie in a
finite subgroup chart, and their group inverses still do not encode Leavitt
star inside `Q` itself.  What the extension supplies is a synchronized
two-sheet coefficient system in which star can be transported exactly.

The live missing operation is now only:

> recover, in matrix coordinates, the cross-root Steinberg multiplication
> relation as support containment between the finite Pauli coefficient cuts.

Equivalently, one must promote the exact ring identity `ef=f` for a
child--parent pair to an inclusion of the corresponding finite multiplicity
supports.  Ambient root-character balance alone cannot do this; it requires a
coherent finite radical quotient, or an equivalent normalizer/character
completion theorem.

## Lean certificate

`GroupApproximation/Sofic/InvolutiveTwoSheet.lean` kernel-checks the exact
finite-dimensional identities:

- the swap is a self-adjoint unitary of order two;
- swap conjugation exchanges the two diagonal blocks;
- diagonal doubling preserves unitarity;
- the diagonal normalized trace is the average of the two old traces;
- every diagonal-times-swap matrix has trace zero;
- doubled Hilbert--Schmidt error is the average of the two sheet errors.

Together with the already formalized subgroup theorem
`isHyperlinear_of_injective`, these are the load-bearing algebraic and metric
steps of the finite-extension proof.  The Lean check was run against the warm
repository build on MSI, not locally.

