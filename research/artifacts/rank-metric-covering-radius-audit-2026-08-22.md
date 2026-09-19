# Rank-metric covering radius versus sparse syndrome distance

Primary source checked: Eimear Byrne and Alberto Ravagnani, *Covering Radius
of Matrix Codes Endowed with the Rank Metric*, SIAM Journal on Discrete
Mathematics 31 (2017), 927--944, DOI `10.1137/16M1091769`,
arXiv `1608.08755`.

The paper defines the covering radius of a matrix code `C` as

```text
rho(C)=max_X min_(Y in C) rank(X-Y).
```

Its Corollary 18 gives the dual-distance bound

```text
rho(C)<=k-d(C^perp)+1
```

for a proper linear code in `F_q^(k by m)`.  The paper also develops external
distance and initial-set upper bounds.  These are exact rank-metric statements
about the nearest matrix in a coset.

For the generator-column sampler, `C=ker(T_E)` and the exact affine minrank of
the ideal syndrome is indeed

```text
min_(Y in C) rank(I-Y).
```

But robust sampled soundness asks instead for

```text
min_(rank(B)<=s) wt_H(T_E(I-B))/|E|.
```

This is Hamming distance **after** the measurement map from the image of a
nonlinear bounded-rank variety.  It is neither the rank covering radius nor a
consequence of the cited dual-distance bound.  In particular an exact coset
may have large minimum rank while its syndrome is at vanishing Hamming
distance from a low-rank syndrome, as
`degree-one-generator-columns-have-sqrt-minrank-but-no-gap` demonstrates.

The audit therefore supports using rank-metric language for the exact affine
fiber, but not importing covering-radius estimates as normalized-HS or
syndrome-distance estimates.
