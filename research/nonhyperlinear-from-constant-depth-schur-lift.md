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

Apply `finite-depth-contractive-computation-ladder` to `(CDS1)`.  The chosen
constant depth gives a dimension-independent number

```text
epsilon_0=a_*^2/(4(K_0+C S_m)^2)>0
```

such that every finite-dimensional tuple satisfying the marked interface has
`E(V)>=epsilon_0`.

If `Gamma_m` were hyperlinear, algebraic nontriviality of `w` and the usual
amplification of canonical microstates would give tuples with relator energy
tending to zero while the marked word stays at the fixed separation used to
derive `a_*`.  This contradicts the displayed energy floor.  Hence
`Gamma_m` is nonhyperlinear.

The infinite tail of the Fanizza computation is used only to prove that the
finite source BCS has a nonzero marked completeness model and supplies the
first `m` exact doubling identities.  It is not represented by an infinite
Schur tower in the finite presentation.
