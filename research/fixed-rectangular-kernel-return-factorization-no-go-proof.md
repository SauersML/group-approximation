---
rg: 2
id: fixed-rectangular-kernel-return-factorization-no-go-proof
kind: route
title: Apply von Neumann rank-nullity and the bilateral regular shift
target: fixed-rectangular-kernel-return-factorization-is-impossible
requires: []
---

Let `N=L(Gamma)` with its canonical finite trace and let
`T=lambda(A):L2(N)^p -> L2(N)^q`.  For a rectangular operator over a finite
von Neumann algebra,

```text
dim_N ker(T)=p-dim_N closure(ran(T)) >= p-q.            (FRK4)
```

On `ker(T)`, equation `(FRK1)` gives

```text
(I_p tensor (lambda(w^2)-1))xi=lambda(C)Txi=0.
```

Decompose `Gamma` into left cosets of the infinite cyclic subgroup
`<w^2>`.  On each coset, `lambda(w^2)` is a bilateral shift.  A fixed vector
would have constant coefficients along an infinite orbit and hence cannot
belong to `l2`; therefore `lambda(w^2)-1` is injective.  Its `p`-fold diagonal
amplification is injective as well, contradicting `(FRK4)`.

For the approximate interpretation, evaluate fixed representatives of the
finitely many group-algebra coefficients of `(FRK1)`.  Telescoping a fixed
derivation of the equality gives

```text
||D_U-C_U A_U||_(2,pd)=o(1),
D_U=I_p tensor (w(U)^2-1).
```

If `P_U` projects onto `ker(A_U)`, ordinary rank-nullity gives
`tr_(pd)(P_U)>=(p-q)/p` and multiplication by `P_U` gives `(FRK3)`.  Since
the block diagonal word has exactly the same normalized scalar moments as
`w(U)^2`, the Fejer-kernel argument of
`unnamed-positive-density-fixed-space-is-terminal` would already contradict
canonical microstates.  The regular argument shows why no fixed algebraic
data with these hypotheses can exist in the first place.
