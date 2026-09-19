---
rg: 2
id: literal-full-group-cstar-nonexact-proof
kind: route
title: Combine the embedded arithmetic lattice with the new factorization theorem
target: literal-full-group-cstar-is-nonexact
requires:
  - literal-group-factorization-property
  - literal-telescope-split-normal-form
  - nonamenable-factorization-groups-have-nonexact-full-cstar
artifacts:
  - research/artifacts/literal-folner-sharp-boundary-2026-08-30.md
---

The split normal form is a retracted inclusion

```text
SL_3(Z) < (Z[1/2]^3 rtimes SL_3(Z)) rtimes Z < E.
```

Since `SL_3(Z)` is nonamenable, so is `E`.  The first prerequisite gives
the factorization property of `E`; the general third prerequisite then
forces nonexactness of `C*_(max)(E)`.
