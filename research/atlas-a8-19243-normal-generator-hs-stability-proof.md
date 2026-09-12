---
rg: 2
id: atlas-a8-19243-normal-generator-hs-stability-proof
kind: route
title: Apply finite normal-generator trivialization to the audited A8 collision involution
target: atlas-a8-19243-normal-generator-hs-stability
requires:
  - finite-normal-generator-hs-trivialization
  - atlas-a4-19243-parabolic-normal-closure
---

The normal-closure audit proves that the repeated collision involution satisfies

```text
<<b>>_A8=A8.
```

Apply `finite-normal-generator-hs-trivialization` to the fixed pair `(A8,b)`.
It supplies a constant `L(A8,b)` such that every exact finite-dimensional
unitary representation `pi` obeys

```text
tr_d(1-Q_pi)
 <= L(A8,b)^2 ||pi(b)-1||_2^2.
```

Taking

```text
C_19243=L(A8,b)^2
```

is exactly `(A8-19243-STAB)`.  Since this constant belongs to the fixed finite
chart group and element, it is independent of the representation dimension and
of every external atlas multiplicity.
