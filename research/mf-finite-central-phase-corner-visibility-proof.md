---
rg: 2
id: mf-finite-central-phase-corner-visibility-proof
kind: route
title: Cut a nontrivial central-character corner and use conjugacy invariance of trace
target: mf-finite-central-phase-corner-visibility
requires: [countable-group-mf-conventions]
---

## Why sufficient

Let the order of `z` be `m>1`.  By
`countable-group-mf-conventions`, choose a faithful homomorphism

```text
u : G -> U(Q),   Q = prod_n M_(d_n) / directSum_n M_(d_n).       (FCP2)
```

For `lambda in mu_m` put

```text
P_lambda = (1/m) sum_(j=0)^(m-1) conj(lambda)^j u(z)^j.          (FCP3)
```

These are the spectral projections of `u(z)`.  They are pairwise orthogonal
and sum to `1`.  Since `u` is faithful and `z != 1`, `u(z) != 1`; hence
`P_lambda != 0` for some `lambda != 1`.  Fix such a `lambda` and write
`P=P_lambda`.

Centrality of `z` makes `P` commute with `u(G)`, so `P` is a nonzero
`G`-invariant corner and

```text
P u(z) = lambda P.                                               (FCP4)
```

As in the standard projection-lifting argument, `P` lifts after restriction
to a sequence of nonzero projections `p_n`, and

```text
PQP = prod_n M_(r_n) / directSum_n M_(r_n),
r_n = rank(p_n) >= 1.                                           (FCP5)
```

The compressed homomorphism `v(a)=P u(a)` is therefore represented by
operator-norm local models `v_n:G->U(r_n)` on exhausting windows.

Compress `(FCP1)`.  In the corner it becomes the exact identity

```text
v(s) v(g) v(s)^* = lambda v(g).                                 (FCP6)
```

Every tracial state `tau` on `PQP` consequently satisfies

```text
tau(v(g)) = tau(v(s)v(g)v(s)^*) = lambda tau(v(g)).              (FCP7)
```

Because `lambda != 1`, `(FCP7)` gives `tau(v(g))=0`.  Applying this to all
free-ultrafilter limits of the normalized coordinate traces shows

```text
tr_(r_n)(v_n(g)) -> 0.                                          (FCP8)
```

(Equivalently, take normalized traces in approximate coordinate versions of
`(FCP6)`; operator-norm error dominates trace error, and divide by the fixed
nonzero scalar `1-lambda`.)  Hence

```text
||v_n(g)-1||_(2,norm)^2
  = 2-2 Re tr_(r_n)(v_n(g)) -> 2.                               (FCP9)
```

Compression costs nothing in operator norm, so a sufficiently late
coordinate meets any prescribed finite window and tolerance.  This is
maximal tracial visibility and supplies the invariant corner required by the
conclusion.  End proof.

