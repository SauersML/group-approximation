---
rg: 2
id: edgeful-or3-balanced-private-plane-packet
kind: claim
title: The edgeful one-ghost clause has a balanced ten-coordinate packet with one private plane per literal
distinct_from:
  edgeful-one-ghost-escape-avoids-term-recurrence: that uses one Hamming edge abstractly; this gives one simultaneous full-support rational packet and three disjoint edges, one for every logical coordinate.
  tracial-bcs-has-rational-balanced-hyperoctahedral-atlas: that obtains some rational local-marginal point from a tracial BCS and may assign zero rank to allowed atoms; this gives a fixed strictly positive point independent of the instance.
---

Write the logical coordinates of `R_edge` as

```text
(a,b,c)=(x_2,x_3,x_4),       x_1=1-a.                   (OBP1)
```

Then `R_edge` is exactly the seven satisfying assignments of
`a OR b OR c`.  Give the three Hamming-weight-one assignments multiplicity
two and the four assignments of weight two or three multiplicity one:

```text
n(100)=n(010)=n(001)=2,
n(110)=n(101)=n(011)=n(111)=1.                           (OBP2)
```

The total dimension is ten, every allowed assignment atom is nonzero, and
each of `a,b,c` has plus and minus ranks `5,5`.

There are three pairwise disjoint coordinate planes, using distinct copies
when an assignment has multiplicity two:

```text
a-plane: 001 -- 101,
b-plane: 100 -- 110,
c-plane: 010 -- 011.                                    (OBP3)
```

Apply a nontrivial Hadamard/Givens rotation on each plane and the identity on
the remaining four coordinates.  The `a`-plane changes logical marginal
`a` and the private complement `x_1`, but fixes `b,c`; the `b`-plane changes
only `b`; and the `c`-plane changes only `c`.  After independent free-phase
wordization, every logical marginal therefore has one private off-diagonal
phase-labelled plane and no off-diagonal contribution from either of the
other two planes.

For signed 3SAT, put the first literal in coordinate `a`, its private
complement in `x_1`, and the other two literals in `b,c`.  Negating a literal
only negates the corresponding marginal and does not change the support or
rank calculation.  Thus every clause has the same full-support balanced
packet and three occurrence-private escape planes.

All context algebra identities are automatic.  If `Y_t` are the diagonal
assignment projections, `U` is the product of the three root rotations, and
`W=sum_i h_i e_i`, then

```text
P_t=W U Y_t U^* W^*                                     (OBP4)
```

are self-adjoint orthogonal projections summing to the corner unit.  No
separate star or idempotence relators are introduced, so those identities
create no additional vertices or short cycles in the coefficient-pairing
link.
