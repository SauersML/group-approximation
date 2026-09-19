---
rg: 2
id: sparse-dyadic-iwahori-boundary-proof
kind: route
title: Use the three characteristic-two coadjoint orbits and a top-down flow estimate
target: sparse-dyadic-iwahori-packets-have-a-uniform-boundary
requires:
  - pure-dyadic-regular-iwahori-mixtures-have-a-uniform-half-loss
---

For `a>=3`, the last principal congruence layer

```text
K_a=ker(G_a->G_(a-1))
```

is the elementary abelian group

```text
1+2^(a-1) sl_2(F_2) = F_2^3.                            (SBP1)
```

It is normal, and conjugation factors through
`G_1=SL_2(F_2)=S_3`.  In coordinates

```text
X=(a,b,c) <-> [[a,b],[c,a]],
```

the dual action has the following nonzero orbits:

```text
{(0,0,1),(0,1,0),(0,1,1)},
{(1,0,0),(1,0,1),(1,1,0)},
{(1,1,1)}.                                               (SBP2)
```

For the upper-root vector `E_12=(0,1,0)`, respectively `1/3`, `2/3`,
and `0` of the characters in these orbits are trivial.  Clifford theory
says that the restriction to `K_a` of an irreducible exact-conductor-`a`
representation is a constant-multiplicity sum over one nonzero orbit: the
zero orbit would make the irreducible trivial on the normal group `K_a`
and hence lower its conductor.  Its `u(2^(a-1))`-fixed fraction is therefore
at most `2/3`.  Direct sums prove `(SDI1)`.  Conjugating gives the lower-root
version.

Let `x_a`, respectively `y_b`, be the physical dimensions of the upper and
opposite exact-conductor bands.  Choose a maximal common edge
subrepresentation and refine it by both source bands; write `c_(a,b)` for
the resulting coupled physical dimension and

```text
u=d-sum_(a,b)c_(a,b)=L/2.                               (SBP3)
```

If `b<=a`, every opposite level-`b` edge representation is trivial on
`M_b`, hence on `M_a subset M_b`.  In the upper level-`a` quotient, the
image of `M_a` contains `u(2^(a-1))`.  Applying `(SDI1)` simultaneously to
the whole part routed to depths `b<=a` gives

```text
sum_(b<=a)c_(a,b) <= (2/3)x_a.                          (SBP4)
```

The symmetric argument in the opposite coordinate gives

```text
sum_(a<=b)c_(a,b) <= (2/3)y_b.                          (SBP5)
```

These are the asserted bidirectional-flow constraints.

Order the at most `K` occupied depth values from top to bottom.  If
`X_>j`, `Y_>j` denote total band dimensions strictly above the current
depth `j`, `(SBP4)--(SBP5)` and the total unmatched mass `u` imply

```text
x_j <= 3u+3Y_>j,       y_j <= 3u+3X_>j.                 (SBP6)
```

Thus, for `T_j=X_>=j+Y_>=j`,

```text
T_j <= 6u+4T_>j.                                       (SBP7)
```

Starting at the top occupied depth and iterating through at most `K`
depths gives

```text
2d=T_bottom <= 6u(1+4+...+4^(K-1))
              =2u(4^K-1).                              (SBP8)
```

Using `(SBP3)` proves `(SDI3)`.  Finally the orthogonal projection of a
unitary comparison onto exact edge intertwiners has squared normalized
norm at most `1-u/d`.  Its distance from the intertwiner space is at least
`sqrt(u/d)>=1/sqrt(4^K-1)`; the uniform congruence spectral gap of the fixed
Iwahori group gives `(SDI4)`.

