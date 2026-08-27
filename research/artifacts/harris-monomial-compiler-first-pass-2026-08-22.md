# Harris-to-monomial compiler: first-pass audit — 2026-08-22

## Target

The phase-safe monomial route starts from the fixed non-CE synchronous game,
uses Harris's equal-size bisynchronous conversion, and seeks one finite-phase
matrix pair whose monomial-isomorphism algebra preserves the source trace and
its absence of matrix-ultraproduct representations.

Harris's canonical magic unitary is block-circulant:

```text
u_((a,x),(i,x))=e_(a-i,x).
```

For an ordinary weighted matrix pair, `uA=Bu` is equivalent to pair-color
preservation.  On a fixed pair of question blocks, direct substitution asks
for scalar colors `alpha(i,j)` and `beta(a,b)` with

```text
alpha(i,j)=beta(a,b)
  iff (a-i,b-j) belongs to the winning support.
```

`harris-circulant-one-matrix-compiler-forces-affine-support` proves that this
is possible exactly when the winning support is a coset of a subgroup of the
answer-pair group.  Thus direct coloring reproduces the affine/LCS boundary
and cannot encode the fixed nonlinear non-CE BCS.

## What remains open

The no-go does not touch three stronger constructions:

1. add incidence vertices that turn a nonlinear predicate into projection
   consistency with a satisfying-tuple variable;
2. use several phase-resolved blocks and retain the source only as a full
   corner; or
3. abandon the Harris circulant completion and construct a different magic
   or quantum-reflection completion adapted to the fixed source trace.

The first option is now the primary monomial gate.  Its acceptance test is
strict: auxiliary blocks must not create a Connes-embeddable trace, and the
perfect non-CE source trace must extend to the completed algebra.  Merely
preserving existence of perfect strategies is insufficient.

## Literature boundary

Harris, Theorem 3.3, preserves the game algebra but produces the circulant
completion above.  Brannan--Gromada--Hernandez Palomares--Priebe, Theorem
5.2, identifies the monomial game algebra for a matrix pair but does not
assert that arbitrary bisynchronous game algebras arise this way.  The gap
between those theorems is therefore real and is not filled by composing
their statements.

