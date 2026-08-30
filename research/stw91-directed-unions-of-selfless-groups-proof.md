---
rg: 2
id: stw91-directed-unions-of-selfless-groups-proof
kind: route
title: Identify the reduced group algebra as a trace-compatible directed union
target: stw91-directed-unions-of-selfless-groups
requires:
  - robert-directed-unions-preserve-selflessness
artifacts:
  - research/artifacts/stw91-selfless-group-frontier-2026-08-30.md
---

For every subgroup `H <= G`, restriction of the left regular representation
of `G` to `H` is a direct sum of copies of the left regular representation of
`H`, indexed by the left cosets `H\G`.  Hence the algebraic inclusion
`C[H] -> C[G]` is isometric for the reduced norms and extends to a unital
embedding

```text
C*_r(H) -> C*_r(G).                                  (1)
```

The canonical traces are compatible with (1), since both take the
coefficient of the identity.  Directedness of `(G_i)` makes the images
`C*_r(G_i)` an upward directed family.  Their union contains every group
unitary `lambda_g`, and therefore contains `C[G]`; its norm closure is
`C*_r(G)`.

Robert's directed-union theorem now applies to the C*-probability spaces
`(C*_r(G_i),tau_i)` and gives selflessness of `(C*_r(G),tau_G)`.  Robert's
uniform-Dixmier theorem for selfless spaces then implies simplicity, so `G`
is C*-simple.

**Trust boundary.**  The only imported mathematical input is Robert's
directed-union permanence theorem.  Reduced-norm injectivity, trace
compatibility, and density are proved above.
