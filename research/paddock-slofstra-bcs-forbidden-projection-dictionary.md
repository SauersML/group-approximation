---
rg: 2
id: paddock-slofstra-bcs-forbidden-projection-dictionary
kind: claim
title: BCS failure mass is exactly a sum of joint spectral projections
distinct_from:
  non-ce-bcs-has-finite-dimensional-forbidden-mass-gap: that obtains a positive lower bound by ultraproduct compactness; this is the exact algebraic identity identifying what is being bounded.
  mipstar-bcs-tracial-nonru-exists: that supplies one separated BCS; this applies to every finite BCS with contexts.
---

Let `B` be a finite BCS with context `U`, relation `R`, and commuting
self-adjoint involutions `(z_x)_(x in U)`.  For an assignment `phi`, put

```text
Pi_(U,phi)=product_(x in U) (1+phi(x)z_x)/2.
```

Paddock--Slofstra's joint-spectral presentation gives mutually orthogonal
projections summing to one, and the relation polynomial `P_R` satisfies

```text
1+P_R(U)=2 sum_(phi notin R) Pi_(U,phi).                (PSD1)
```

Consequently the normalized trace of the right-hand projection is exactly the
probability that the joint context measurement violates `R`.  Quotienting by
`P_R(U)=-1` is equivalent to killing every forbidden atom individually.

Their perfect-strategy dictionary also identifies tracial states on the BCS
algebra with perfect commuting-operator strategies, and homomorphisms to
`R^U` with perfect quantum-approximable strategies.  Thus the
tracial/non-`R^U` source gap and the forbidden-mass formulation refer to the
same concrete joint spectral projections.
