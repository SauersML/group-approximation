---
rg: 2
id: tag-centralized-successor-corner
kind: claim
title: Centralizing each two-bit tag on the next occurrence makes its survivor the recurrent corner
distinct_from:
  two-bit-tag-routing-splits-s3-exit-and-survivor: that constructs the exit/survivor partition but does not relate the survivor to the next occurrence; this adds precisely the off-diagonal tag-to-occurrence commutators which make that analytic survivor a reducing corner.
  free-occurrence-hnn-return-does-not-preserve-first-hit-prefix: that gives a countermodel when the return chart and pulse are independent; here the endpoint table is transported into the very tag table defining the prefix.
---

Let `H_x`, `x in X`, be a Thompson orbit of freely amalgamated occurrences,
sharing only a central involution `J`.  In `H_x` let `K_x,b_x` be commuting
endpoint involutions which commute with its shared BCS words.  Put a commuting
two-bit tag `(T_(x,1),T_(x,2))` at every site, and impose

```text
[T_(x,i),y_z]=1                         (x!=z)          (TSC1)
```

for every shared generator `y_z` of the occurrence at `z`.  For a bridge
`u_x` impose

```text
u_x J u_x^*=J,
u_x K_x u_x^*=T_(x,1),
u_x b_x u_x^*=T_(x,2),
[u_x,T_(z,i)]=1                         (z!=x).          (TSC2)
```

Choose distinct sites `x_0,x_1,...`, let

```text
E_n=(1-T_(x_n,1))(1-T_(x_n,2))/4,
S_n=1-E_n,
C_0=1,                 C_n=product_(j<n)S_j,
Q=(1-J)/2.                                              (TSC3)
```

If the source endpoint table is restricted to the reducing carrier
`R_n=C_nQ`, then its exit and live projections

```text
P_exit=R_n(1-K_(x_n))(1-b_(x_n))/4,
P_live=R_n-P_exit                                      (TSC4)
```

satisfy

```text
u_(x_n)P_exit u_(x_n)^*=C_nQE_n,
u_(x_n)P_live u_(x_n)^*=C_(n+1)Q.                     (TSC5)
```

The second projection in `(TSC5)` reduces every shared word in the next
occurrence `H_(x_(n+1))`.  The first projections are pairwise orthogonal, so
their traces have total at most one.  In particular, the exit charged at
level `n` is literally absent from every later carrier.

There is a polynomial normalized-HS version.  At depth `n`, exactify the
finite endpoint/tag/prefix table together, and let `E` be the sum of the
squared named-relator defects.  The two errors in `(TSC5)` and the leakage of
the returned live projection across any fixed next-occurrence word are at
most

```text
p(n)sqrt(E)                                             (TSC6)
```

for a computable polynomial `p`, independent of matrix dimension.

The infinite families in `(TSC1)--(TSC2)` have a finite presentation.  The
rational-tail action of Thompson `V` has one diagonal and one off-diagonal
ordered-pair orbit and finitely generated point stabilizers, so one prototype
of each relation generates its whole orbit.  Standard prefix transporters
give polynomial derivation area.

Exact marked completeness is retained.  Fold all occurrence copies onto the
same amplified marked occurrence, represent every tag pair by its endpoint
pair `(K,b)`, take every bridge to be the identity, and let `V` act trivially.
Endpoint centrality on the shared BCS words verifies `(TSC1)`, while `(TSC2)`
is immediate.  Thus no new relation kills the retained marked word.

