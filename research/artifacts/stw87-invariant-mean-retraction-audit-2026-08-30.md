# STW LXXXVII: invariant-mean retraction audit (2026-08-30)

## Result

For a countable amenable group `G` with a proper left-invariant
bounded-geometry metric, an invariant mean gives a conditional expectation

```text
C*_u(G)=ell^infinity(G) crossed_product_r G -> C*_r(G)
```

by coefficient averaging.  If `G` has a subgroup of finite index `k>=2`,
the expectation sends the `k` orthogonal coset projections to the same
scalar `1/k`.  This packet has exact distance `1/k` from every c.p.c.
order-zero map from `C^k` to `C*_r(G)`.

The proof is internal: the expectation is obtained by compressing the
regular covariant representation associated to the GNS representation of
the invariant mean.  The lower bound follows because an element less than
`1/k` away from `(1/k)1` is invertible, whereas two images of different
minimal projections under an order-zero map must be orthogonal.  The zero
map attains the lower bound.

## Consequence for the open problem

For `G=Z^d`, the inclusion `C*_r(G)=C(T^d) subset C*_u(G)` therefore has a
u.c.p. retraction, but this retraction does not preserve, or admit uniformly
small repairs of, outgoing order-zero colours.  Hence quotient permanence
of nuclear dimension cannot be imitated merely by replacing a quotient map
with the invariant-mean expectation.  The result does not determine
`dim_nuc(C*_u(Z^2))`; it removes one otherwise plausible route to the
missing lower bound.
