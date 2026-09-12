---
rg: 2
id: leavitt-omega-has-an-explicit-distorted-target-proof
kind: route
title: Shift x13 twice and read the surviving x15(s0 squared) Steinberg root
target: leavitt-omega-has-an-explicit-distorted-target
requires:
  - leavitt-nielsen-collision-has-a-hidden-first-side-relation
---

The source calculation gives

```text
Omega(x_12(s_0),qp)=1.                               (DT1)
```

For the target put `A=x_13(s_0)` and `B=p`.  Two conjugations by the 20-cycle
shift both root indices by two:

```text
B^2AB^(-2)=x_35(s_0).                                (DT2)
```

The two roots in `(DT2)` form one Steinberg chain, so in characteristic two

```text
Omega(A,B)=[x_13(s_0),x_35(s_0)]
          =x_15(s_0s_0).                             (DT3)
```

This is nonidentity.  On the standard Leavitt module, apply it to the basis
vector in matrix coordinate `5` with an arbitrary infinite binary tail
`omega`.  Its image is the sum of that vector and the coordinate-`1` vector
with word `00 omega`; the second summand cannot cancel.

The artifact verifies `(DT1)--(DT3)` without truncation.  For every deletion
operator it partitions all possible initial binary cylinders and retains the
unexamined tail as an opaque symbol.  The target calculation itself contains
no deletion and its displayed moved vector is literal.

If a relative presentation forced one element to conjugate both source
generators to the target generators, `(DT1)` would imply `(DT3)=1`, killing a
nontrivial element in a single coefficient copy.  No such one-equation
transport is asserted here.
