---
rg: 2
id: polynomial-compressor-has-explicit-finite-quotient-wall
kind: claim
title: The polynomial property-T compressor has an explicit positive-density finite-quotient wall
artifacts:
  - experiments/polynomial_compressor_finite_wall.py
distinct_from:
  property-t-hs-positive-density-commutant-no-growth: that upper-bounds every positive-density compressed commutant wall by microstate defect; this constructs one exact finite quotient in which such a wall is visibly nonzero.
  schur-packet-as-positive-density-compressor-wall: that must identify the predicate Reynolds difference with a compressor wall in every marked microstate; this supplies the concrete compressor and a nonzero wall but not the predicate coupling.
  packet-kazhdan-commutant-placement-decouples: that refutes a packet placed on an independent tensor factor; this wall is intrinsic to the original and compressed images of the same group representation.
---

Let

```text
Gamma=EL_3(F_2[x,y]),
alpha:Gamma->Gamma,       alpha(x)=x, alpha(y)=xy.       (PFW1)
```

The map `alpha` is injective, `Gamma` has property `(T)`, and the quotient
ring

```text
R=F_2[x,y]/(x^2-x,y^2-y,xy)
```

is `F_2^3`, by evaluation at `(0,0),(1,0),(0,1)`. Put
`G=SL_3(F_2)=EL_3(F_2)`. The induced finite quotient of `(PFW1)` has

```text
B=q(Gamma)=G^3,
A=q(alpha(Gamma))={(g_0,g_1,g_0):g_0,g_1 in G} ~= G^2. (PFW2)
```

In particular `[B:A]=|G|=168`.

Let `rho=lambda_B` be the left regular representation of `B` on a space of
dimension `d=|B|`. On adjoint space, the fixed subspaces of `B` and `A` are
their operator commutants. Their dimensions are

```text
dim rho(B)'=|B|,
dim rho(A)'=[B:A]|B|=168|B|.                            (PFW3)
```

Thus the compressed-minus-original Reynolds projection is a genuine wall of
normalized adjoint density

```text
tr_ad(R_A-R_B)=167/|B|>0.                               (PFW4)
```

All data are fixed and finite. This proves that the established polynomial
compressor has enough exact representation-theoretic room for a
positive-density wall. It does not yet solve the Schur placement: one must
make the forbidden packet Reynolds range land in this intrinsic wall by
shared coefficient-covariance relations. Bare tensor-factor commutation
still fails.

There is a decisive canonical-profile limitation.  The quotient kernel is
infinite, so `fixed-finite-quotient-adjoint-walls-are-canonical-trace-null`
shows that every adjoint sector carrying this fixed quotient action has zero
density in canonical delta microstates of `Gamma`.  Thus `(PFW4)` is a finite
test module, not by itself the positive-density wall required by the
nonhyperlinearity argument.
