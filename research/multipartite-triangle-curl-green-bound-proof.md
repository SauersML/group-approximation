---
rg: 2
id: multipartite-triangle-curl-green-bound-proof
kind: route
title: Invert the two commuting averaging projections blockwise
target: multipartite-triangle-curl-has-uniform-infinity-green-bound
requires: []
---

The clique complex of a complete `r`-partite graph is connected and has
vanishing first cohomology for `r>=3`.  Thus the Moore--Penrose edge
representative is orthogonal to vertex gradients, equivalently divergence
free.  Summing its triangle curl over the `q=(r-2)m` possible third vertices
of an oriented edge gives

```text
S_(ab)=q f(a,b)
       +sum_(a' in part(a)) f(a',b)
       +sum_(b' in part(b)) f(a,b').
```

This already yields the coarse estimate: at an edge maximizing `|f|`, the
two last sums have total magnitude at most `2m||f||_infinity`, while
`|S_(ab)|<=q||delta_1 f||_infinity`.  Hence for `r>=5`,

```text
(r-4)m||f||_infinity
 <=(r-2)m||delta_1 f||_infinity.
```

For the sharp all-`r` estimate, identify the values between two parts with
an `m by m` matrix and let `R,L` average respectively along its rows and
columns.  They are commuting projections, and the same exact sum gives on
the divergence-free space

```text
delta_1^* delta_1 = T=qI+m(R+L).
```

The four joint `(R,L)` eigenspaces have eigenvalues `q,q+m,q+m,q+2m`.
Direct substitution therefore verifies

```text
T^(-1)=aI+b(R+L)+cRL,
a=1/((r-2)m),
b=-1/((r-2)(r-1)m),
c=2/(r(r-1)(r-2)m):
```

its eigenvalues are respectively
`1/((r-2)m),1/((r-1)m),1/((r-1)m),1/(rm)`.
The divergence-free space is invariant under `T`, and `delta_1^*` lands in
it, so `T^(-1)delta_1^*` is the Moore--Penrose Green operator.

Fix one output edge.  Among the input triangles, the numbers whose two
corresponding endpoints agree with it in both, exactly one, or neither
coordinate are

```text
q,  2q(m-1),  q(m-1)^2.
```

Their Green coefficients are, respectively,

```text
a+2b/m+c/m^2,  b/m+c/m^2,  c/m^2.
```

For integers `r>=3,m>=1`, the outer two are positive and the middle one is
nonpositive (it is zero only when `r=3,m=1`).  The exact absolute row sum is
therefore

```text
B_(r,m)
=1+2(m-2)/((r-1)m)+2(m-2)^2/(r(r-1)m^2).
```

Put `x=(m-2)/m`, so `-1<=x<1`.  This is a convex quadratic in `x`; its
value at `x=1` exceeds its value at `x=-1` by `4/(r-1)`.  Hence

```text
B_(r,m)<=1+2(r+1)/(r(r-1)).
```

The right side decreases for integer `r>=3` and equals `7/3` at `r=3`.
This proves the claimed dimension-free infinity norm bound, including the
coarser recovery estimate and every stated endpoint constant.
