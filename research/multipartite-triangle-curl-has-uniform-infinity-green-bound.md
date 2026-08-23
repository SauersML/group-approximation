---
rg: 2
id: multipartite-triangle-curl-has-uniform-infinity-green-bound
kind: claim
title: Complete multipartite triangle curl has a uniform infinity Green bound
distinct_from:
  full-torus-prime-power-reynolds-column-is-multipartite-triangle-curl: that identifies the arithmetic column with this simplicial operator; this constructs the dimension-free inverse estimate.
  scalar-reynolds-cb-norm-is-the-infinity-norm: that identifies scalar cb norm with infinity norm abstractly; this bounds that infinity norm for the multipartite family.
---

**ESTABLISHED.**  Let `K_(m,...,m)` be the complete `r`-partite graph,
with `r>=3`, and let

```text
delta_1:C^1 -> C^2,
(delta_1 f)(a,b,c)=f(a,b)+f(b,c)+f(c,a)                (MTG1)
```

on antisymmetric edge functions and triangles whose vertices lie in three
different parts.  On `ker(delta_1)^perp`, with the standard counting
inner products, the following dimension-free bound holds for every
`r>=3`:

```text
||delta_1^dagger||_(infinity -> infinity)
 <= B_(r,m)
 :=1+2(m-2)/((r-1)m)+2(m-2)^2/(r(r-1)m^2)
 <=1+2(r+1)/(r(r-1))<=7/3.                            (MTG2*)
```

The domain of the inverse is `ran(delta_1)` with its inherited infinity
norm.  In particular, for `r>=5` the following coarser direct recovery
estimate also holds:

```text
||f||_infinity
 <= ((r-2)/(r-4)) ||delta_1 f||_infinity.              (MTG2)
```

Equivalently, the coarse estimate is

```text
||delta_1^dagger||_(infinity -> infinity)
 <= (r-2)/(r-4),                                       (MTG3)
```

The bounds are independent of the part size `m`.

Here is an explicit recovery proof.  Since the clique complex is connected
and has `H^1=0`, `ker(delta_1)=im(delta_0)`.  Hence the Moore--Penrose
representative `f in ker(delta_1)^perp` is divergence free:

```text
sum_(b adjacent to a) f(a,b)=0.                        (MTG4)
```

Put `Y=||delta_1 f||_infinity`, fix an oriented edge `a in i`, `b in j`,
and sum `(MTG1)` over all `(r-2)m` vertices `c` in parts other than `i,j`.
The orientation is

```text
S_(ab)=sum_c [f(a,b)+f(b,c)+f(c,a)].                   (MTG5)
```

Using `(MTG4)` first at `b` and then at `a` gives the exact identity

```text
S_(ab)
 =(r-2)m f(a,b)
   +sum_(a' in i) f(a',b)
   +sum_(b' in j) f(a,b').                             (MTG6)
```

Indeed the omitted `i`-part in the divergence sum at `b` changes sign by
antisymmetry, while the omitted `j`-part at `a` already has the displayed
orientation.  Hence

```text
|S_(ab)| <= (r-2)mY,
|sum_(a' in i)f(a',b)|+|sum_(b' in j)f(a,b')|
 <=2m||f||_infinity.
```

Choose an edge attaining `||f||_infinity` and apply the reverse triangle
inequality to `(MTG6)`.  This gives

```text
(r-4)m||f||_infinity <= (r-2)mY,
```

which is `(MTG2)`.

Here is the sharper symmetry calculation proving `(MTG2*)`.  For two
different parts `i,j`, write the edge values between them as an `m` by
`m` matrix `G_(ij)`.  Put

```text
q=(r-2)m,
R(G)=m^(-1)(G 1)1^T,          L(G)=m^(-1)1(1^T G).    (MTG7)
```

The projections `R,L` commute.  If `f` is divergence free, summing over
the third vertex exactly as in `(MTG6)` gives the block formula

```text
(delta_1^*delta_1 G)_(ij)
 =qG_(ij)+(G_(ij)1)1^T+1(1^T G_(ij))
 =(qI+m(R+L))G_(ij).                                  (MTG8)
```

The positive operator on the right is invertible on the full matrix
block.  Its inverse is

```text
T^(-1)=aI+b(R+L)+cRL,
a=1/((r-2)m),
b=-1/((r-2)(r-1)m),
c=2/(r(r-1)(r-2)m).                                  (MTG9)
```

Although `(MTG8)` was derived on the divergence-free space, that space is
invariant under `T`; hence `T^(-1)delta_1^*` is exactly the Moore--Penrose
Green operator (and gives a harmless extension from all triangle
cochains).

Fix an oriented edge `(x,y)`.  In the corresponding row of
`T^(-1)delta_1^*`, classify a triangle `(x',y',z)` according as both, one,
or neither of `x'=x` and `y'=y` hold.  The counts are respectively

```text
q,          2q(m-1),          q(m-1)^2,               (MTG10)
```

and the coefficients are

```text
a+2b/m+c/m^2,       b/m+c/m^2,       c/m^2.           (MTG11)
```

For `r>=3`, the first and third coefficients are positive and the middle
one is negative.  Therefore the absolute row sum is exactly

```text
q(a+2b/m+c/m^2)
-2q(m-1)(b/m+c/m^2)
+q(m-1)^2 c/m^2
=B_(r,m).                                              (MTG12)
```

This proves the first inequality in `(MTG2*)`.  Writing
`x=(m-2)/m in [-1,1)` shows that `B_(r,m)` is a convex quadratic in `x`;
its supremum occurs at `x->1` and is

```text
1+2(r+1)/(r(r-1)).                                    (MTG13)
```

This decreases with `r>=3` and equals `7/3` at `r=3`, completing the
uniform estimate.

For the arithmetic family already identified in
`full-torus-prime-power-reynolds-column-is-multipartite-triangle-curl`,
where `p>3` and hence `r=p+1>=6`, `(MTG2*)` is at most `22/15` (and is
strictly smaller at every finite `m`).  The abstract estimate also covers
`r=3,4`; no additional arithmetic square-class identification is asserted
there.
Combined with
`full-torus-prime-power-reynolds-column-is-multipartite-triangle-curl`,
this proves a depth-independent scalar infinity/cb inverse bound for every
full-torus prime-power column in the two-square-class case.  It does not
cover proper subtori, the repeated-square-class case, or nonlinear
continuation away from exact endpoints.
