---
rg: 2
id: hyperlinear-hs-stable-is-rf-proof
kind: route
title: Stable unitary microstates give separating linear images and finite quotients
target: hyperlinear-hs-stable-is-residually-finite
requires: []
---

Fix a finite presentation `G=<S|R>` and `g!=1`.  Hyperlinearity supplies
finite-dimensional unitary tuples `U_n` whose relator defects tend to zero
and for which the word `g(U_n)` stays a fixed normalized-HS distance from the
identity (indeed its normalized trace tends to zero in canonical group-trace
microstates).

Strict same-dimension HS stability perturbs `U_n`, in the same matrix size,
to an exact representation `rho_n:G->U(d_n)` with generator distance tending
to zero.  Word telescoping for the fixed word `g` gives

```text
||rho_n(g)-g(U_n)||_2 -> 0.
```

Thus `rho_n(g)!=1` for all sufficiently large `n`.  Finite-dimensional
unitary representations therefore separate every nonidentity element of
`G`: the group is maximally almost periodic.

Choose one such `rho` with `rho(g)!=1`.  Since `G` is finitely generated,
`rho(G)` is a finitely generated linear group, hence residually finite by
Malcev's theorem.  A finite quotient of `rho(G)` separates `rho(g)` from the
identity, and its pullback separates `g` in `G`.  Since `g` was arbitrary,
`G` is residually finite.
