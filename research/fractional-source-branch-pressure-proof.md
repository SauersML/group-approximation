---
rg: 2
id: fractional-source-branch-pressure-proof
kind: route
title: Apply the Gram capacity inequality at each target and read the coverage bounds into a rational matrix
target: fractional-source-branch-pressure
requires:
  - gram-branching-capacity-with-overlap
  - rational-supercritical-branch-certificate
---

**`(FSB1)`.**  Fix a target `j` and apply `gram-branching-capacity-with-overlap`
with `P=P_j` and the family of incoming partial isometries `{T_e : e -> j}`.  Its
`(GBC2)` reads

```text
x_j >= sum_(e: ->j) tau(E_e) - 2 l_j - o_j,
```

where `l_j` and `o_j` are exactly the leakage and ordered-pair Gram sums defined
above.  Note that `(GBC1)`--`(GBC2)` place no constraint on the source
projections `E_e` beyond their being the sources of partial isometries, so
`E_e <= P_i` strictly smaller than `P_i` is already inside its scope; this is
the only step where partial coverage could have failed, and it does not.

Substituting the coverage bounds `(FSB0)`,

```text
sum_(e: ->j) tau(E_e) >= sum_(e: i->j) (c_e x_i - a_e)
                       = (Bx)_j - sum_(e: ->j) a_e,
```

gives `x_j >= (Bx)_j - eta_j`, which is `(FSB1)`.

**`(FSB3)`.**  The derivation `(RBC1) => (RBC3)` in
`rational-supercritical-branch-certificate` uses only that the matrix is
nonnegative and that `x,e,y >= 0`:

```text
kappa (y . x) = ((1+kappa)y - y) . x
              <= (B^T y - y) . x
              = y . (Bx) - y . x
              <= y . (x + eta) - y . x
              = y . eta.
```

Integrality of the matrix is never used, so the certificate step transfers
verbatim from the integer matrix `A` of that node to the rational matrix `B`
here.  (Alternatively, clear denominators: `B = A/N` for an integer matrix `A`
and integer `N`, and `A^T y >= N(1+kappa)y`.)

**Two-child corollary.**  With states ordered `(P,R_0,R_1)` the branch matrix is

```text
B = [[0, q_0, q_1],
     [1,   0,   0],
     [1,   0,   0]],
```

whose characteristic polynomial is `-z(z^2 - (q_0+q_1))`, so
`rho = sqrt(q_0+q_1)`.  When `q_0+q_1>1` the matrix restricted to the strongly
connected component `{P,R_0,R_1}` is irreducible with `rho>1`.  An explicit
rational certificate is available whenever `q_0,q_1` are rational: pick any
rational `kappa>0` with `(1+kappa)^2 <= q_0+q_1` and set

```text
y = (1, q_0/(1+kappa), q_1/(1+kappa)).
```

Then `(B^T y)_(R_i) = q_i = (1+kappa) y_(R_i)` with equality, and
`(B^T y)_P = (q_0+q_1)/(1+kappa) >= (1+kappa) = (1+kappa) y_P`, so `(FSB2)`
holds.  Checking it is exact rational arithmetic.
