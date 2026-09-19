---
rg: 2
id: fanizza-compression-implies-localized-square-return
kind: route
title: Square the compressed verifier reflection and discard the verifier payload
target: localized-square-return-wandering-promotion
requires:
  - fanizza-coherent-verifier-wandering-promotion
---

Use the group, carrier `Q`, and ordinary word `w` from the coherent Fanizza
promotion.  Clause 1 gives

```text
||Q_U w(U) Q_U-V_m(U)||_2=o(1),
V_m(U)^2=Q_U.
```

Equations `(CFP1)--(CFP4)` with `m=2` give

```text
||(w(U)^2-1)Q_U||_2=o(1).
```

The fixed packet has positive canonical mass, and clause 3 makes `w` have
infinite order.  Clause 4 supplies the exact consistency/nontriviality
witness.  These are precisely the localized square-return requirements.
The native signal clause and the marked translates are not used.

