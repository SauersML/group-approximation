---
rg: 2
id: finite-order-normal-generation-controls-corona-rank-scale-proof
kind: route
title: Compare exact torsion spectral ranks through a fixed normal word
target: finite-order-normal-generation-controls-corona-rank-scale
requires:
  - matrix-corona-projection-ideal-and-corner-calculus
  - corona-representations-have-an-ideal-valued-support-length
---

Write `ord(a)=m` and `ord(b)=ell`.  Choose unitary coordinate lifts of the
finitely many group elements in a fixed normal word

```text
b = product_(j=1)^N h_j a^(epsilon_j) h_j^(-1),
epsilon_j in {+1,-1}.
```

Finite-spectrum rounding replaces the lift of `rho(a)` by unitaries `A_n`
with `A_n^m=1`, and the lift of `rho(b)` by unitaries `B_n` with
`B_n^ell=1`, without changing their corona classes.  If `H_(j,n)` are
unitary lifts of the conjugators, put

```text
W_n=product_(j=1)^N H_(j,n) A_n^(epsilon_j) H_(j,n)^*.
```

The normal-word identity in the corona gives

```text
||B_n-W_n|| -> 0.                                    (P1)
```

Let `p_(a,n)` be the active spectral projection of `A_n`.  Each factor
`H_(j,n) A_n^(epsilon_j) H_(j,n)^*` is the identity off a subspace of
dimension `rank(p_(a,n))`.  The product `W_n` is therefore the identity off
the sum of those `N` subspaces, and hence

```text
rank(W_n-1) <= N rank(p_(a,n)).                       (P2)
```

Every nonzero singular value of `B_n-1` is at least

```text
eta_ell=min{|1-zeta|:zeta^ell=1,zeta!=1}>0.
```

For all sufficiently large `n`, `(P1)` is smaller than `eta_ell`.
The singular-value minimax principle then implies

```text
rank(B_n-1) <= rank(W_n-1).                           (P3)
```

Since `rank(B_n-1)=rank(p_(b,n))`, `(P2)` and `(P3)` prove `(NRS1)`.
The matrix-corona projection comparison theorem converts the eventual rank
bound into `(NRS2)`.  The finite-order support formula

```text
Supp_rho(x)=I(p_x)
```

then gives `(NRS3)`.

Apply the same argument to a normal word expressing `a` through `b` to get
the reverse comparison in `(NRS4)`.  Equal principal ideals make both active
projections full in that common ideal, so their corners are Morita
equivalent.  In a simple group every nonidentity element normally generates,
which gives the final statement.

