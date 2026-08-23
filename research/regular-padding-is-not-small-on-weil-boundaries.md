---
rg: 2
id: regular-padding-is-not-small-on-weil-boundaries
kind: claim
title: Regular congruence padding is not a qualitative small repair for rank-one Weil boundaries
distinct_from:
  congruence-induction-cannot-reconstruct-a-low-rank-bs14-boundary: that shows induction costs the subgroup index times the boundary rank; this shows padding by even one regular global quotient costs the full quotient order.
  bs14-native-cells-cross-every-length-cutoff: that proves the exact involution couples a short source to arbitrarily long exits; this combines that family with the size of the proposed regular padding and rules out a diagonal short-hull repair.
  regular-quotient-padding-repairs-exactly-the-restriction-lattice: that characterizes algebraic existence at one fixed quotient; this proves its regular-packet implementation has the wrong asymptotic size even on a lattice-compatible native boundary.
---

**ESTABLISHED NO-GO FOR REGULAR PADDING.**  On the compressed even-Weil
family at primes `p=1 mod 4`, the active missing source has rank one and lies
in the trivial length-one BS packet, while the exact involution couples it
with squared norm `1-1/p` to nonzero packets of length `ord_p(4)`.  The
compressed dimension is

```text
d_p=(p-1)/2.                                             (RCW1)
```

It has no exact same-dimensional endpoint, but restoring one native line
recovers the even-Weil representation.  Therefore any repair operation
which is required to pad by whole copies of the regular representation of

```text
Q_p=PSL_2(F_p)
```

must use at least one copy, of dimension

```text
|Q_p|=p(p^2-1)/2.                                       (RCW2)
```

Consequently its padding ratio satisfies

```text
k_p/d_p >= p(p+1),                                      (RCW3)
```

and diverges, although the native repair has rank one and the presentation
defect tends to zero.

This also refutes the proposed diagonal staircase:

```text
delete long sources;
take the BS hull of sources of length at most M;
apply a fixed-level regular-representation padding theorem;
let M=M(e) grow slowly.                                 (RCW4)
```

In `(RCW1)` the source length is already one for every `M`, so its BS hull
has rank one.  Nevertheless its exact `X`-cell leaves that hull and reaches
an orbit whose length, prime level, and quotient order are unbounded.  Thus
there is no finite quotient or padding constant depending only on `M` to
diagonalize against.  Choosing the actual moving quotient instead incurs
`(RCW3)`, which is not `o(d_p)` at any rate.

Regular padding is therefore useful only after a global atom has already
been authenticated and its restriction-lattice class is correct.  It
cannot perform the active-hull authentication itself.  This no-go is
separate from the passive low-operator-norm basin: it concerns the discrete
active cell even in an exact native congruence family.
