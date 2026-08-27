---
rg: 2
id: depthwise-pauli-packets-have-canonical-regular-escape
kind: claim
title: Every finite-depth common-sign Pauli challenge has a canonical regular escape
distinct_from:
  leavitt-prefixes-form-exponential-heisenberg-packet: that constructs arbitrarily large exact packets with one common sign; this tests any one fixed packet against the depthwise canonical estimate and exhibits an exact canonical-profile countermodel.
  dyadic-parity-checksum-has-finite-pauli-gauge: that gives one stationary nine-cycle gauge for a particular checksum recurrence; this applies to the full finite Heisenberg table at every rank.
  reverse-kleene-unconditioned-collapse-forces-fd-invisibility: that derives finite-dimensional invisibility from an already proved unconditional collapse estimate; this proves that the finite Pauli relations themselves cannot supply such an estimate.
---

**ESTABLISHED.**  Let `H_D` be the binary finite Heisenberg group generated
by involutions

```text
X_1,...,X_D,Z_1,...,Z_D,J
```

with `J` central and

```text
[X_i,X_j]=[Z_i,Z_j]=1,
[X_i,Z_j]=J^(delta_(i,j)).                              (DPR1)
```

Then `J!=1`, `|H_D|=2^(1+2D)`, and the left regular representation
`lambda_D` is an exact finite-dimensional model of the complete packet.  Its
normalized trace is exactly the canonical trace on `H_D`:

```text
tr(lambda_D(g))=0                    for every g!=1,    (DPR2)
```

while

```text
||lambda_D(J)-I||_2^2=2.                                (DPR3)
```

Consequently, consider any proposed fixed-depth estimate whose premise uses
only the relations `(DPR1)` and a canonical trace window consisting of
nonidentity elements of `H_D`:

```text
||J(U)-I||_2^2
 <= b_D+C_D(def_D(U)+sep_D(U)).                         (DPR4)
```

Substitution of `lambda_D` gives

```text
2<=b_D.                                                 (DPR5)
```

This conclusion is independent of the size of `C_D`.  Hence a sequence of
finite-depth common-sign Pauli packets, by itself, cannot realize the
depthwise canonical condition `b_D->0`, even though the union of all depths
forces every exact finite-dimensional representation to kill `J`.

## Proof

Write elements in normal form

```text
J^epsilon X_1^a_1...X_D^a_D Z_1^b_1...Z_D^b_D.
```

The standard Schrödinger representation shows that `(DPR1)` is consistent
with `J!=1`, while the normal form gives at most `2^(1+2D)` elements; the
usual multiplication law on
`F_2 x F_2^D x F_2^D` gives exactly that many.  In the left regular
representation a nonidentity element permutes the group basis without fixed
points, proving `(DPR2)`.  Since `J` is a nonidentity involution,

```text
||lambda_D(J)-I||_2^2
 =tr((lambda_D(J)-I)^*(lambda_D(J)-I))
 =2-2 Re tr(lambda_D(J))=2,
```

which is `(DPR3)`.  All defects and all trace-separation terms in `(DPR4)`
vanish on `lambda_D`, proving `(DPR5)`.

## Scope and the surviving positive target

The theorem does not refute a depth-`D` compiler which adds relations outside
the finite packet and thereby prevents the regular model from extending.
It says exactly what those extra relations must accomplish: each fixed depth
must already couple the packet to the **same marked carrier** through a
dimension-free, canonical-profile obstruction.  Merely increasing the Pauli
rank, and then choosing the rank as a function of matrix dimension, has the
wrong quantifier order for `depthwise-canonical-kleene-needs-no-uniform-runtime-gap`.

