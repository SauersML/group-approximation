---
rg: 2
id: full-torus-prime-power-reynolds-column-is-multipartite-triangle-curl
kind: claim
title: Full-torus prime-power Reynolds columns are multipartite triangle curls
distinct_from:
  prime-power-reynolds-column-does-not-tensor-over-reduction: that uses a rank certificate to refute passive tensoring at level 25; this identifies the exact coupled simplicial operator and proves that rank algebraically.
  constrained-reynolds-column-has-a-diagonal-scalar-shadow: that gives the signed Hecke column for arbitrary congruence quotients; this identifies it with a classical triangle coboundary in the full-torus, two-square-class family.
---

**ESTABLISHED; EXACT CHARACTER-FIBER REDUCTION.**  Let

```text
O=Z/p^k Z,       G=PSL_2(O),       H=<h(2)>,
```

and assume that `H` is the full projective split torus.  Put

```text
m=p^(k-1),       r=p+1.
```

The projective line `P^1(O)` is partitioned by reduction modulo `p` into
`r` fibers of size `m`.  Two projective points form a basis of `O^2`
exactly when they lie in different fibers.  Hence the graph of transverse
pairs is the complete `r`-partite graph

```text
K_(m,...,m).                                             (MTC1)
```

The stabilizer in `G` of the ordered transverse pair `(infinity,0)` is
`H`, and the Weyl element reverses that pair.  Therefore

```text
Ind_(<H,w>)^G chi
```

is canonically the space of antisymmetric scalar functions on the oriented
edges of `(MTC1)`.  This is exactly the domain `(DSS2)` of the scalar
Reynolds column.

Under this identification the first cubic row of `(DSS3)` is triangle
curl on the `G`-orbit of the cyclic triangle

```text
(infinity,-1,0),
```

and the second is triangle curl on the orbit of

```text
(infinity,-1/2,0).                                      (MTC2)
```

Indeed the three fixed input edges in the first row are

```text
(infinity,-1), (0,infinity), (-1,0),
```

because `A=w u(1)` cycles `infinity,-1,0`; the second calculation is the
same with `B=w h(2)u(1/2)`, which cycles `infinity,-1/2,0`.  Right
translation by `q^(-1)` transports these prototype curls to every row.

The square class of

```text
det(v_1,v_2) det(v_2,v_3) det(v_3,v_1)                 (MTC3)
```

classifies the two `PSL_2(O)`-orbits of transverse cyclic triangles.
The prototypes in `(MTC2)` have square classes `1` and `2`.  Consequently,
when `2` is nonsquare modulo `p`, the two Reynolds blocks together are the
entire simplicial coboundary

```text
delta_1:C^1(K_(m,...,m)) -> C^2(K_(m,...,m)),           (MTC4)
```

with every cyclic triangle repeated three times by its order-three
stabilizer.  Row repetition does not change the inherited infinity norm on
the range, so the infinity norm of `C_G^dagger` is exactly the infinity
Green norm of `(MTC4)` on `ker(delta_1)^perp`.

The clique complex of a complete `r`-partite graph is the join of its `r`
discrete vertex sets.  For `r>=3` it has vanishing first cohomology.
Therefore

```text
ker(delta_1)=im(delta_0),
rank(delta_1)=E-V+1
 = binom(r,2)m^2-rm+1.                                  (MTC5)
```

For `p=5,k=2`, `(MTC5)` gives

```text
rank(C_G)=15*25-30+1=346,                               (MTC6)
```

which upgrades the modular lower certificate in
`prime-power-reynolds-column-does-not-tensor-over-reduction` to an exact
algebraic rank computation.

This also identifies the congruence-kernel character decomposition.  The
new root-direction modes are precisely the mean-zero Fourier modes within
the `m` vertices of each residue fiber.  They are coupled by triangle curl;
they are not passive tensor copies.  Conversely, no divergent mode follows
from their mere multiplicity.  The exact remaining full-torus question is

```text
sup_(r,m) ||delta_1^dagger||_(infinity -> infinity)
```

for the complete multipartite clique complexes in `(MTC1)` (with `r=p+1`
and the arithmetic normalizations above).  A bounded simplicial
contraction proves the scalar prime-power estimate in this family; an
unbounded multipartite Green kernel refutes it.  Fourier decomposition
alone is not an infinity-norm proof, because recombining the mean-zero
fiber characters is not unconditional in `l_infinity`.

If `2` is square, the two prototypes in `(MTC2)` lie in the same square
class, so the identification with the *full* triangle coboundary does not
follow.  If `H` is a proper subtorus there is also the extra torus label
from `(DSS9)`.  Neither case is claimed here.

