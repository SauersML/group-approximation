---
rg: 2
id: sync4-coordinate-atom-normal-form-proof
kind: route
title: Fourier-expand a four-outcome PVM into two commuting involutions
target: sync4-coordinate-atom-normal-form
requires: []
artifacts:
  - research/artifacts/culf-mastel-sync-normal-form-2026-08-23.md
---

Let `(E_(u,v))_(u,v in F_2)` be a four-outcome PVM and define

```text
A=sum_(u,v)(-1)^u E_(u,v),
B=sum_(u,v)(-1)^v E_(u,v).
```

Orthogonality of the atoms makes `A` and `B` commuting self-adjoint
unitaries.  Their joint spectral projections recover the PVM by the
Fourier formula

```text
E_(u,v)=1/4 (1+(-1)^u A)(1+(-1)^v B).
```

Conversely, if `A,B` are commuting involutions, these four products are
orthogonal projections and sum to `1`, so the constructions are inverse.
Expanding `R_(u,v)=1-2E_(u,v)` gives

```text
R_(u,v)=1/2(1-(-1)^u A-(-1)^v B-(-1)^(u+v)AB),
```

and `R_(u,v)` is a self-adjoint unitary because it is the reflection of a
projection.

For any two atoms `E,F` with reflections `R=1-2E`, `S=1-2F`,

```text
||E-F||_2^2 = (1/4)||R-S||_2^2
            = (1/4)||(R-S)S||_2^2
            = (1/4)||RS-1||_2^2,
```

using unitary invariance of the tracial Hilbert--Schmidt norm.  Applying
this to the selected endpoint atoms on every `SYNC_4` edge proves the
normal form claimed in `(S4N1)--(S4N4)`.
