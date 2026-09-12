---
rg: 2
id: leavitt-corner-equivalence-gives-one-sided-lift
kind: route
title: Read the primitive projection as the reverse product
target: leavitt-corner-one-sided-lift-exists
requires:
  - leavitt-e-f-murray-von-neumann-equivalence
  - leavitt-primitive-corner-recursive-extension
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
---

The first prerequisite supplies `x,y in eSe` with `xy=e` and `yx=f`; the
second supplies `pi(e)=1`, `pi(f)=s_0t_0`, and `s_0t_0 != 1`.  Therefore

```text
xy=e,        pi(yx)=pi(f)=s_0t_0 != 1,
```

which is exactly `leavitt-corner-one-sided-lift-exists`.  Its existing
corner-padding route then gives a direct-finiteness counterexample in `S`.
