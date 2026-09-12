---
rg: 2
id: expander-incidence-l2-l1-separation-proof
kind: route
title: Unit flow across an expander has bounded L2 residual but logarithmic L1 correction cost
target: l2-angle-does-not-imply-l1-integer-hoffman
requires: []
---

Take any fixed-degree connected expander family `X_n=(V_n,E_n)` with
combinatorial Laplacian gap

```text
lambda_2(X_n)>=gamma>0
```

and `|V_n|->infinity`.  Orient the edges and let `partial_n` be the signed
vertex-edge incidence matrix.  Since

```text
partial_n partial_n^*=Delta_(X_n),                    (ELP1)
```

the nonzero singular values of `partial_n` are the square roots of the
nonzero Laplacian eigenvalues.  Hence

```text
dist_2(x,ker partial_n)
 <=gamma^(-1/2)||partial_n x||_2                      (ELP2)
```

uniformly in `n`.  Every column has two nonzero entries and every row has
the fixed graph degree.

Choose vertices `s_n,t_n` at graph distance `D_n=diam(X_n)` and let `x_n`
be the integral unit flow along a shortest path from `s_n` to `t_n`.  Then

```text
partial_n x_n=delta_(t_n)-delta_(s_n),
||partial_n x_n||_1=2.                                (ELP3)
```

For any real (hence also any integer) cycle flow `z in ker partial_n`, the
flow `y=x_n-z` has the same boundary.  Test it against the one-Lipschitz
vertex function `f(v)=dist(s_n,v)`.  Discrete summation by parts gives

```text
D_n=|<f,partial_n y>|
    =|<partial_n^*f,y>|
    <=||y||_1.                                        (ELP4)
```

Taking `z=0` gives equality, so

```text
dist_1(x_n,ker_R partial_n)
 =dist_1(x_n,ker_Z partial_n)=D_n.                     (ELP5)
```

Fixed-degree graphs with growing order have `D_n->infinity` (indeed at
least logarithmically along a bounded-degree family), proving `(LHI2)`.

For a nonnegative version, replace each edge by its two directed arcs.  The
all-ones arc flow `h_n` lies in the integer kernel.  After choosing the path
orientation, `x_n+N h_n` is nonnegative for `N>=1`, and translation by the
kernel vector preserves both sides of `(ELP3)--(ELP5)`.  Finally split each
signed incidence column into its nonnegative head and tail columns to write
`partial_n=R_(n,+)-R_(n,-)`.

