---
rg: 2
id: spherical-candidate-pairwise-codegrees-proof
kind: route
title: Separated cap intersections sit in a strictly smaller cap
target: spherical-candidate-pairwise-codegrees
requires:
  - trace-separation-sphere-distance-concentration
---

Realify `C^d` as `R^(2d)` and write `n=2d`.  A radius-one ball around a unit
vector `a` cuts the sphere in the cap

```text
||y-a|| <= 1  iff  Re <y,a> >= 1/2.
```

Suppose two unit centers satisfy `Re<a,b> <= 1/4`.  If `y` lies in both
radius-one caps, then

```text
Re<y,a+b> >= 1,
||a+b||^2 = 2+2 Re<a,b> <= 5/2.
```

Therefore, with `c=(a+b)/||a+b||`,

```text
Re<y,c> >= 1/||a+b|| >= sqrt(2/5) > 1/2.
```

So the intersection of the two radius-one caps is contained in a cap with a
strictly larger fixed threshold `c'=sqrt(2/5)`.

For a uniform point on `S^(n-1)`, the first coordinate has density
proportional to `(1-t^2)^((n-3)/2)`.  If `P_n(c)` denotes the cap probability
`Pr[X_1>=c]`, then for fixed `1/2<c'<1`, comparing the numerator integral over
`[c',1]` with a fixed subinterval of the denominator integral over `[1/2,1]`
gives constants `C<infinity` and `theta<1`, independent of `n`, such that

```text
P_n(c') / P_n(1/2) <= C theta^((n-3)/2).
```

Hence the true measure of the intersection of two radius-one caps whose
centers have real inner product at most `1/4` is `o(p_d)`, exponentially so,
where `p_d=P_(2d)(1/2)`.

It remains to verify that almost every input point produces separated centers.
For `w != w'`, put `D=U_w^*U_w'`.  The established claim
`trace-separation-sphere-distance-concentration` gives

```text
E |<x,Dx>-tau(D)|^2 <= 1/(d+1).
```

Since `tau(D)=o(1)`, Markov/Chebyshev implies

```text
Pr[ Re<U_w x,U_w' x> > 1/4 ] = O(1/d)+o(1).
```

There are only finitely many tested word pairs, so all but an `o(1)` fraction
of input sphere points are simultaneously good for every pair.

For such a good input `x_i`, and for an independent output sample point
`x_j`, membership in `N_w(i)` has probability `p_d`, while simultaneous
membership in `N_w(i)` and `N_w'(i)` has probability `q_d=o(p_d)`.  Choose
`N(d)` so that `N p_d` dominates the logarithmic union-bound cost (there is no
restriction against taking `N` exponentially large in `d`).  Standard
binomial Chernoff bounds then make all degrees `(1+o(1))Np_d` and all good
pair codegrees `o(Np_d)` simultaneously, except for the already `o(N)` bad
input vertices.  This proves the claim.
