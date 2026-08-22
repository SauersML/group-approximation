---
rg: 2
id: sl3-noncorrectable-lambda-sector-has-no-projective-leak
kind: claim
title: Uniformly noncorrectable canonical SL3 lattice microstates have no projective arithmetic leak
distinct_from:
  sl3-odd-correctable-sector-has-uniform-projective-modulus: that proves projective transfer after correction to congruence representations of level coprime to p; this asks for the complementary sector uniformly far from every exact finite-dimensional lattice representation.
  fixed-projective-gap-forces-primary-congruence-mass: that constrains the p-primary mass inside an available exact correction; this applies where no such correction exists at all.
  sl3-canonical-double-has-a-correctable-vertex: that would remove this sector by proving at least one vertex is correctable; this asks directly for absence of a projective leak without first correcting the vertex.
---

OPEN.  Let `rho_n` be canonical-character normalized-HS microstates of

```text
Gamma=SL_3(Z[1/p])
```

whose restrictions to `Lambda=SL_3(Z)` stay at a uniform positive
generator distance from every exact finite-dimensional representation of
`Lambda`.  If unitaries `U_n` satisfy

```text
sum_(c in S_Lambda)
 (1-|tr([U_n,rho_n(c)])|^2)->0,                         (UNC1)
```

then

```text
1-|tr([U_n,rho_n(h)])|^2->0.                            (UNC2)
```

This is the exact sector not touched by congruence conductor, parahoric
branching, or shell-PVM arguments.  Proving it directly, or proving that a
canonical arithmetic microstate always has a correctable lattice vertex,
is independently necessary for full
`projective-commutant-transfer-for-arithmetic-pair`.

## Attempts

Property `(T)` does not directly control this sector: the adjoint maps of a
normalized-HS microstate are still only an approximate representation, so
the Kazhdan projection cannot be applied before an exactification step.
Correcting that adjoint representation is precisely the special stability
statement already isolated in the parent PRCC claim, and general HS
stability of `SL_3(Z)` is false.  The attack is therefore deferred until one
uses an arithmetic denominator relation to exactify the adjoint lift or
proves the alternative one-correctable-vertex theorem.
