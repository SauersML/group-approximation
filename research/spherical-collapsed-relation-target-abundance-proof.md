---
rg: 2
id: spherical-collapsed-relation-target-abundance-proof
kind: route
title: A midpoint cap sits inside both next-target caps, then Chernoff fills it
target: spherical-collapsed-relation-target-abundance
requires: []
---

Fix a root `i` with `eta_i<=1/16` and an `h`-candidate `j`.  Since the
unitaries preserve distance,

```text
||b-a||
 <= ||U_g x_j-U_g U_h x_i|| + ||(U_gU_h-U_k)x_i||
 <= 1+1/16 = 17/16.
```

For unit vectors this means

```text
t=Re<a,b>
 =1-||a-b||^2/2
 >= 1-(17/16)^2/2
 =223/512.
```

Let

```text
c=(a+b)/||a+b||.
```

Then

```text
Re<c,a>=Re<c,b>=sqrt((1+t)/2)
                     >= sqrt(735)/32.
```

The numerical bound `sqrt(735)>24` gives

```text
Re<c,a>, Re<c,b> > 3/4.
```

If a unit vector `y` satisfies `||y-c||<=1/4`, then

```text
Re<y,a> >= Re<c,a>-||y-c|| > 1/2,
Re<y,b> >= Re<c,b>-||y-c|| > 1/2.
```

For unit vectors, `||y-a||<=1` is equivalent to `Re<y,a>>=1/2`, and likewise
for `b`.  Thus the radius-`1/4` ball around `c` is contained in the
intersection of the two radius-one target caps.

Now condition on `x_i,x_j`.  For every `l` different from `i,j`, the cloud
point `x_l` is independent and uniform, so membership in this contained
radius-`1/4` ball is Bernoulli with success probability exactly `q_d`.
The number of such shared targets therefore stochastically dominates
`Bin(N-2,q_d)`.  Chernoff gives failure probability `exp(-Omega(N q_d))` for
the lower bound `(1-o(1))Nq_d`.  There are only `O(N^2)` candidate pairs per
relation and finitely many tested relations, so `N q_d >> log N` makes the
union bound simultaneous.

Finally, for a uniform sphere point,

```text
E eta_i^2 = ||U_gU_h-U_k||_2^2,
```

with the normalized Hilbert--Schmidt convention.  The random variables
`eta_i^2` are iid and bounded by `4`.  If the table defect tends to zero,
Markov (or Hoeffding after fixing a small threshold) gives an `o(1)` fraction
of roots with `eta_i>1/16`, simultaneously over the finite relation set.
