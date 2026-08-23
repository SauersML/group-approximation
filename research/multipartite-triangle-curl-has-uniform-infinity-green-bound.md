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
with `r>=5`, and let

```text
delta_1:C^1 -> C^2,
(delta_1 f)(a,b,c)=f(a,b)+f(b,c)+f(c,a)                (MTG1)
```

on antisymmetric edge functions and triangles whose vertices lie in three
different parts.  On `ker(delta_1)^perp`, with the standard counting
inner products,

```text
||f||_infinity
 <= ((r-2)/(r-4)) ||delta_1 f||_infinity.              (MTG2)
```

Equivalently,

```text
||delta_1^dagger||_(infinity -> infinity)
 <= (r-2)/(r-4),                                       (MTG3)
```

where the domain of the inverse is `ran(delta_1)` with its inherited
infinity norm.  The bound is independent of the part size `m`.

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

For the arithmetic family `r=p+1` with `p>3`, `(MTG3)` is at most `2`.
Combined with
`full-torus-prime-power-reynolds-column-is-multipartite-triangle-curl`,
this proves a depth-independent scalar infinity/cb inverse bound for every
full-torus prime-power column in the two-square-class case.  It does not
cover proper subtori, the repeated-square-class case, or nonlinear
continuation away from exact endpoints.
