---
rg: 2
id: stw93-full-null-implies-residual-null
kind: route
title: Pull a residual quasitrace back and annihilate the original trace kernel
target: stw93-residual-trace-kernel-is-quasitrace-null
requires:
  - stw93-jiang-su-slice-ideal-is-quasitrace-null
  - stw93-trace-kernel-quasitracial-invisibility
---

Let `q-bar` be a normalized `2`-quasitrace on `D/K_𝒵`.  Its pullback
`q=q-bar∘π` is a normalized quasitrace on `D`, so full trace-kernel
invisibility gives `q(I_+)=0`.  Every positive element of `I/K_𝒵` has a
positive lift in `I`: if `y≥0` lies in `π(I)`, standard positive lifting
for the quotient map on `I` gives `x∈I_+` with `π(x)=y`.  Hence

```text
q-bar(y)=q(x)=0.
```

Therefore every normalized quasitrace on the quotient annihilates the
residual ideal.
