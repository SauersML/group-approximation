---
rg: 2
id: finite-quotient-diagonal-koopman-sector-proof
kind: route
title: Pull mean-zero functions on one finite quotient into the diagonal of every deeper regular quotient
target: canonical-congruence-adjoint-complement-is-not-tempered
requires: []
---

Write `r_n:Q_n->>Q_0` for the quotient map.  For
`f in l^infinity(Q_0)`, let `D_(f,n)` be the diagonal multiplication
operator on `l^2(Q_n)` given by

```text
D_(f,n) delta_x = f(r_n(x)) delta_x.                     (DKS1)
```

The fibers of `r_n` have equal size, so

```text
tr_(Q_n)(D_(f,n)^*D_(k,n))
 = |Q_0|^(-1) sum_(y in Q_0) conjugate(f(y)) k(y).        (DKS2)
```

Thus `f |-> x_f=[D_(f,n)]` is an isometry from `l^2(Q_0)` into
`L^2(M)`.  Left translation gives the exact covariance

```text
rho_n(g)D_(f,n)rho_n(g)^* = D_(g.f,n),                   (DKS3)
```

so this is the Koopman representation of the left action of `Gamma` on
`Q_0`.

Now suppose `f` has mean zero.  For `g=e`,
`tr_(Q_n)(D_(f,n)^*rho_n(g))=0` by the mean-zero assumption.  For fixed
`g!=e`, residuality gives `g notin N_n` for all sufficiently large `n`.
Then left translation by the nonidentity element `gN_n` has no fixed point
on `Q_n`, so its permutation matrix has zero diagonal and

```text
tr_(Q_n)(D_(f,n)^*rho_n(g))=0.                            (DKS4)
```

The group unitaries span an `L^2`-dense subspace of `iota(L(Gamma))`.
Equations `(DKS2)`--`(DKS4)` therefore put the whole copy of
`l^2_0(Q_0)` inside the complement `K` in `(CAT2)`.  Since the left action
on `Q_0` is transitive, this mean-zero representation has no
`Gamma`-invariant vector.

It remains to prove non-temperedness.  The kernel `H` acts trivially on
`l^2_0(Q_0)`.  If this nonzero finite-dimensional representation were
weakly contained in `lambda_Gamma`, restriction to `H` would give

```text
1_H weakly contained in lambda_Gamma|_H.
```

Because `H` has finite index,
`lambda_Gamma|_H` is a finite direct sum of copies of `lambda_H`.
Hulanicki's criterion would then make `H` amenable.  But a finite-index
subgroup of the nonamenable group `Gamma` is nonamenable, a contradiction.
Hence `l^2_0(Q_0)` is not weakly contained in `lambda_Gamma`, proving
`(CAT3)`.

Finally, if `C<A` has the same image as `A` in every finite quotient, then
the restriction of `(DKS3)` to `C` is still the transitive left-regular
action of `Q_0`; its only fixed functions are constants.  This explains why
the counterexample kills full-complement temperedness but creates no
`C`-fixed mean-zero leak.
