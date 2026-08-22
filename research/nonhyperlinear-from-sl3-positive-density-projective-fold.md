---
rg: 2
id: nonhyperlinear-from-sl3-positive-density-projective-fold
kind: route
title: Apply a phase-twisted finite Fejer window to the positive fold singular sector
target: non-hyperlinear-group
requires:
  - sl3-positive-density-projective-fold-sector
---

Let

```text
w=i_0(h)i_1(h)^(-1) in D=A *_C A.                       (PFF1)
```

Because `h notin C`, the word `w` is cyclically reduced of amalgam length
two.  Every positive power `w^k` is reduced and nontrivial.  Thus the
canonical character vanishes on all nonzero powers of `w`.

Assume, toward a contradiction, that `D` has canonical microstates satisfying
`sl3-positive-density-projective-fold-sector`.  Put

```text
W_n=H_(n,0)H_(n,1)^*,       X_n=H_(n,1)Y_n,
V_n=conjugate(lambda_n) W_n.                             (PFF2)
```

Then `X_n` is a contraction with the same normalized-HS mass as `Y_n`, and

```text
||(V_n-1)X_n||_2
 =||(H_(n,0)-lambda_n H_(n,1))Y_n||_2 ->0.              (PFF3)
```

Fix an integer `N` with `N alpha>1`, and put

```text
B_N(z)=sum_(j=0)^(N-1) z^j,
F_N(z)=N^(-1) B_N(z)^* B_N(z).                          (PFF4)
```

The telescoping estimate in
`unnamed-positive-density-fixed-space-is-terminal` applies to `(V_n,X_n)`
and gives

```text
liminf_n tr(F_N(V_n)) >= N alpha>1.                     (PFF5)
```

On the other hand, for every fixed `0<|k|<N`, canonicality and `(PFF1)` give

```text
tr(V_n^k)
 =conjugate(lambda_n)^k tr(W_n^k) ->0.                  (PFF6)
```

Word-evaluation errors between `W_n^k` and the chosen representative of
`w^k` also tend to zero because `k` is fixed.  Expanding the positive Fejer
polynomial therefore gives

```text
tr(F_N(V_n)) ->1,                                       (PFF7)
```

contradicting `(PFF5)`.  Hence `D` is non-hyperlinear.

The proof consumes a genuinely finite window: the fixed presentation
relators and the moments of `w^k` for `0<|k|<N`.  Once `alpha` is known, no
convergence-rate comparison, full character classification, or correction
of either vertex is needed.  The finite-window envelope supplies no missing
arithmetic estimate; it only certifies that the positive-sector assertion,
if proved, already terminates in one fixed normalized-HS obstruction.
