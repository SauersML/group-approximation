---
rg: 2
id: d16-charge-of-two-leavitt-branches-is-collapse-or-zero
kind: claim
title: The D16 charge of two depth-one Leavitt branches either collapses the children or reads zero
distinct_from:
  paired-same-reservoir-boundary-lemma: that asks for a finite-matrix same-reservoir-or-boundary theorem and already isolates one coarse-to-fine support row; this tests the separate two-path Hadamard charger on the two native branch returns.
  hadamard-selector-commutator-charges-two-path-leakage: that gives a positive charge for two unitary endomorphisms of one common source; this proves the Leavitt branch maps do not furnish such a pair compatibly with exact completeness.
  literal-prefix-three-root-swap-retains-typed-carriers: that gives the typed finite countermodel for one partial swap; this compares both sibling swaps and their closed source holonomies.
---

# The D16 charge of two depth-one Leavitt branches either collapses the children or reads zero

ESTABLISHED.  In the binary Leavitt algebra put

```text
e=s_0t_0,
f_i=s_(0i)t_(0i),
x_i=s_(0i)t_0,
y_i=s_0t_(0i)                         (i=0,1).          (DLB1)
```

Prefix cancellation gives the complete depth-one Gram table

```text
y_i x_j=delta_(ij)e,
x_i y_j=s_(0i)t_(0j),
f_0 f_1=0.                                                (DLB2)
```

The ordinary three-elementary words

```text
J_i=[[1-f_i,x_i],[y_i,1-e]]                              (DLB3)
```

are involutions and satisfy

```text
J_i ehat J_i^*=fhat_i.                                   (DLB4)
```

There are only two natural ways to feed these branches into the D16
two-path charger.

## Forward swaps: the charge destroys completeness

Suppose a selector-central return `d` had diagonal blocks `J_0,J_1`.
The transverse D16 relator forces those blocks equal.  But `(DLB4)` would
then give

```text
fhat_0=J_0 ehat J_0^*=J_1 ehat J_1^*=fhat_1.            (DLB5)
```

Together with `fhat_0 fhat_1=0`, this forces both fine children to vanish.
Thus charging the difference of the two **forward** partial swaps is
incompatible with the nonzero exact Leavitt model.  Approximate equality
likewise charges the genuine separation of the two fine labels, not escape
from their common multiplicity reservoir.

## Closed returns: the charge is identically zero

If each branch is closed back to the coarse source before comparison, its
source holonomy is

```text
y_i x_i=e.                                                (DLB6)
```

On the `e` corner both returned unitaries are therefore the identity.  The
D16 block pair is `(I_e,I_e)`, so its Hadamard commutator has zero defect in
the exact Leavitt model and in the finite rectangular model.  The information
distinguishing the children is the crossed coefficient

```text
y_i x_j=0                  (i!=j),                       (DLB7)
```

which is a partial-isometry/Gram statement, not a unitary holonomy on the
common source.

The missing selector-central word is therefore not an accidental syntax
choice.  The formal piecewise operator

```text
q J_0+(1-q)J_1                                           (DLB8)

```

would place the forward swaps in D16 blocks, but it is an additive
controlled group-algebra element rather than a native group word, and its
charger would impose the false equality `(DLB5)`.  Aligning the two target
labels by the native branch swap before returning instead makes the two
blocks equal tautologically and restores the zero-energy rectangular escape.

Consequently the D16 two-path cell cannot prove the depth-one
same-reservoir boundary lemma.  The viable Leavitt datum remains exactly the
one-sided support row: authenticate that `x_i` has nearly full source Gram
inside one common coarse/fine packet carrier, or charge its wrong-target
component.  That is not reducible to comparing the two closed unitary branch
holonomies.

