# Fresh relative-corner root equivalence (2026-08-30)

## Result

Restricting the arbitrary actuator to a genuinely fresh relative word fixes
the identity-return contradiction, but it does not make the requested
contraction easier than the nonhyperlinear-group root once either of the
consumer's composability requirements is retained:

1. if the output preserves the ambient free-product embedding, one fresh edge
   already has canonical corner mass exactly `alpha^2`; or
2. without that embedding, the simultaneous pairwise target violates the
   finite tracial capacity bound when `L` and then `M` are large.

Conversely, any explicit finitely presented nonhyperlinear group makes both
universal microstate clauses vacuous after taking a free product, while the
perfect exact model extends trivially.  Hence both corrected targets are
root-equivalent in the intended effective finitely presented category.

## 1. The exact free baseline

Let `H` be the packet group, let `q in C[H]` be a projection, and write

```text
q=sum_(h in H) a_h h,   alpha=tau(q)=a_1>0.
```

For `r=v^(-1)w` in the free product `H*F(v,w)`, normal form gives

```text
r^(-1) h r k=1  iff  h=k=1.
```

Therefore

```text
||q r q||_2^2
 =tau(q r^(-1) q r q)
 =tau(r^(-1) q r q)
 =a_1^2
 =alpha^2.                                             (FRC1)
```

This is sharp: it is attained in the free product itself.  Canonical-profile
microstates converge on the fixed group-ring polynomial in `(FRC1)`.
Thus an actuator bound

```text
limsup ||q r q||_2^2 <= alpha rho^(2L)
```

with `rho^(2L)<alpha` rules out hyperlinearity.

## 2. The batched capacity inequality

For pairwise fresh letters put `Q_i=v_i q v_i^*`.  In a canonical-profile
microstate limit,

```text
tau(Q_i)=alpha,
tau(Q_i Q_j)<=alpha rho^(2L)   (i!=j).
```

With `S=sum_i Q_i`, tracial Cauchy--Schwarz gives
`tau(S)^2<=tau(S^2)`.  Hence

```text
M^2 alpha^2
 <= M alpha+M(M-1)alpha rho^(2L),
```

equivalently

```text
M(alpha-rho^(2L)) <= 1-rho^(2L).                       (FRC2)
```

Choose first `L` with `rho^(2L)<alpha`, then

```text
M>(1-rho^(2L))/(alpha-rho^(2L)).
```

This contradicts `(FRC2)`.

## 3. Converse and the honest weaker boundary

Given an explicit finitely presented nonhyperlinear group `N`, free-product
every requested output with `N`.  Free-product normal form preserves the
input subgroups.  The distinguished perfect representation extends by sending
`N` to the identity.  Because hyperlinearity passes to subgroups, the output
is nonhyperlinear and there is no canonical-profile microstate sequence, so
the universal contraction clauses hold vacuously.

A non-root-strength repair must therefore stop at the sharp Haar/free
baseline `alpha^2`, bound `L` or `M`, allow selected density to decay,
or give up the ambient embedding/iterative composability needed downstream.
