---
rg: 2
id: pauli-guard-collapses-c18-to-three-bit-recurrence
kind: claim
title: The prescribed Pauli guard collapses Fanizza C18 to the three-bit projection recurrence
distinct_from:
  fanizza-c18-residual-factors-through-three-tiny-rank-gates: that factors the full six-bit truth table through an even-parity guard; this proves that the native multiplicative Pauli relation makes that guard identically active.
  fanizza-native-additive-incidence-is-one-triangle: that treats the six context variables as independent Boolean coordinates and obtains one flat cycle; this uses the prescribed word relation and removes the cycle.
---

**REFUTED.**  The displayed identity `(PGC3)` is not a defining relation of
the native Fanizza algebra and fails on the terminal block of its exact HALT
representation.  See
`fanizza-pauli-guard-switches-off-at-the-terminal-cell`.  The calculation
below is valid only after adding `(PGC3)` as an extra relation; that addition
destroys the marked completeness model and therefore cannot be used on the
native groupification lane.

Write the six C18 sign bits as two triples.  With `-1` represented by bit
one, Fanizza's forbidden set is

```text
A_123 x A_456,
A_123={100,010,001,110,111},
A_456={000,011,101,110}.                               (PGC1)
```

The second set is exactly the even-parity subset of three bits.  In the
native algebra its three involutions are

```text
(J, X_tilde Z_tilde X_tilde, Z_tilde),                (PGC2)
```

and the multiplicative Pauli relation is

```text
X_tilde Z_tilde X_tilde Z_tilde=J,
J^2=1.                                                 (PGC3)
```

Therefore their product is one:

```text
J (X_tilde Z_tilde X_tilde) Z_tilde=1.                (PGC4)
```

Their joint spectrum is supported entirely on `A_456`.  Equivalently, if
`z` is the bit of `Z_tilde`, the last triple is `(j,j+z,z)` and has even
parity for both values of `j,z`.

Consequently C18 is violated exactly when the first triple lies in `A_123`.
Its allowed first-triple set is

```text
{000,011,101}.                                         (PGC5)
```

If those bits are the projections `(p,q,r)`, `(PGC5)` is precisely

```text
p q=0,       p+q=r.                                    (PGC6)
```

Thus the six-variable predicate is exactly the one-step projection-doubling
recurrence once the already retained multiplicative Pauli relations are
used.

## Quantitative form

For approximate involutions put

```text
H_456=(1+J X_tilde Z_tilde X_tilde Z_tilde)/2.         (PGC7)
```

Then

```text
||H_456-1||_2
 <= (1/2)(||X_tilde Z_tilde X_tilde Z_tilde-J||_2
          +||J^2-1||_2).                              (PGC8)
```

After exactifying the fixed commuting C18 context, let `F_123` be the
first-triple forbidden projection and `F_C18=F_123 H_456`.  Since
`||F_123||<=1`,

```text
||F_C18-F_123||_2 <= ||H_456-1||_2.                   (PGC9)
```

The usual fixed-context exactification adds only its dimension-independent
`O(sqrt(E))` term.  Hence replacing C18 by the three-bit recurrence loses a
fixed computable amount controlled by the already named Pauli relators; no
new matrix-coordinate decoder is used.

## Incidence consequence

The additive recurrence context no longer contains `Z_tilde`.  The chord

```text
C_Z --(Z_tilde)-- C_R
```

disappears, while the multiplicative Pauli equation remains an ordinary
group relation.  The remaining nonlinear context hypergraph has the join
tree with center `C_D` and leaves `C_X,C_Z,C_R`.  Therefore native additive
cycle compatibility is not an open problem; only prescribed-word/corner
realization on this join tree remains.
