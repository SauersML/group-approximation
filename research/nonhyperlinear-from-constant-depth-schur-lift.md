---
rg: 2
id: nonhyperlinear-from-constant-depth-schur-lift
kind: route
title: A constant Schur prefix already forces the marked HS energy floor
target: non-hyperlinear-group
requires:
  - self-referential-bcs-doubling-tape
  - constant-depth-schur-lift-of-doubling-tape
  - finite-depth-contractive-computation-ladder
---

Apply `finite-depth-contractive-computation-ladder` to `(CDS1)` only for
tuples with `||w(V)-I||_2>=rho`, where `0<rho<sqrt(2)` is fixed in the
constant-depth lift.  The chosen constant depth gives a
dimension-independent number

```text
epsilon_0=a_*^2/(4(K_0+C S_m)^2)>0
```

such that every finite-dimensional tuple satisfying the marked interface has
`E(V)>=epsilon_0`.

If `Gamma_m` were hyperlinear, algebraic nontriviality of `w` would give
canonical microstates with relator energy tending to zero and
`tr(w(V))->0`.  In particular,
`||w(V)-I||_2^2=2-2 Re tr(w(V))->2`, so these tuples eventually satisfy
the stated separation hypothesis.  This contradicts the displayed energy
floor.  Hence `Gamma_m` is nonhyperlinear.

The infinite tail of the Fanizza computation is used only to prove that the
finite source BCS has a nonzero marked completeness model and supplies the
first `m` exact doubling identities.  It is not represented by an infinite
Schur tower in the finite presentation.
