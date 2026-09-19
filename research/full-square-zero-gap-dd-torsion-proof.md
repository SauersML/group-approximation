---
rg: 2
id: full-square-zero-gap-dd-torsion-proof
kind: route
title: Cut at the uniform gap and use the finite-rank projective corner
target: full-square-zero-gap-forces-dd-torsion
requires: []
---

Fullness of `x` says exactly that `x_t` is nonzero for every `t in X`.
The norm function of a continuous-trace field is continuous, so compactness
of `X` gives the displayed positive minimum `m`.

Assume there are `lambda in (0,m)` and `gamma>0` such that

```text
dist(lambda,spectrum(|x_t|)) >= gamma       for every t in X.
```

After decreasing `gamma`, assume
`gamma<min(lambda,m-lambda)`.  Choose a continuous
function `f:[0,infinity)->[0,1]` which is zero on
`[0,lambda-gamma]` and one on `[lambda+gamma,infinity)`.  Since every fiber
spectrum misses the transition interval, functional calculus gives

```text
p=f(|x|),       p^2=p=p*.
```

Also `f(0)=0`, so `p` belongs to `A`, rather than merely its multiplier
algebra.  Each `p_t` is finite-rank because `|x_t|` is compact and the cutoff
is bounded away from zero.  It is nonzero because
`||x_t||>=m>lambda`.  Norm-continuity of the projection field makes its rank
locally constant; connectedness of `X` therefore gives one finite positive
rank `r` on all fibers.  In particular, `p` is full.

The square-zero relation supplies the promised orthogonal copy.  On the
joint spectrum choose a continuous function `g`, vanishing near zero, which
equals `1/s` above the gap, and set

```text
v=x g(|x|),       q=vv*.
```

Then `v*v=p`, so `q` is a projection Murray--von Neumann equivalent to `p`.
Moreover

```text
(x*x)(xx*)=x* x^2 x*=0.
```

Functional calculus for orthogonal positive elements gives `pq=0`.  Thus
`p` and `q` are orthogonal equivalent full finite-rank projections.

Finally, the full corner `pAp` is a locally trivial `M_r`-bundle over `X`
and is Morita equivalent to `A`, so it represents the same
Dixmier--Douady class.  Here is the torsion calculation rather than an appeal
to it.  On a trivializing cover, lift the `PU(r)` transition functions of
`pAp` to `U(r)`-valued functions `u_ij`.  On triple overlaps,

```text
u_ij u_jk u_ki = c_ijk 1_r
```

for a circle-valued Cech 2-cocycle `c` representing `DD(A)`.  Taking
determinants gives

```text
det(u_ij) det(u_jk) det(u_ki) = c_ijk^r.
```

Thus `c^r` is the coboundary of the circle-valued 1-cochain
`det(u_ij)`, so `r DD(A)=0`.  Equivalently, the determinant of `U(r)` kills
the obstruction to lifting the transition functions through

```text
circle -> U(r) -> PU(r)
```

This proves that `DD(A)` is torsion.
