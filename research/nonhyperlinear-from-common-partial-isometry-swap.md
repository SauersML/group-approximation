---
rg: 2
id: nonhyperlinear-from-common-partial-isometry-swap
kind: route
title: Apply the static game gap to one common partial-isometry swap
target: non-hyperlinear-group
requires:
  - oracularizable-tracial-nonru-game-exists
  - one-gram-vector-decodes-a-finite-bcs-strategy
  - partial-isometry-swap-wordizes-one-bcs-gram-row
  - perfect-tracial-bcs-has-one-common-module-swap
  - common-partial-isometry-swap-game-compiler
---

Let `Gamma,J,S` be supplied by the compiler.  Exact completeness gives one
representation with `J!=I`, hence `J!=1_Gamma`.

If `Gamma` were hyperlinear, canonical-trace microstates would have relator
defect tending to zero and

```text
tau(J)->0,
tau((I-J)/2)->1/2.                                    (NCPS1)
```

The compiler and `(NCPS1)` give

```text
liminf ||S||_2^2>=gamma/2.                            (NCPS2)
```

The commutator comparison bounds every BCS Gram row by a fixed multiple of
the corresponding literal group-relator defect, so the total game energy
`E_S` tends to zero.  The finite game gap instead gives

```text
E_S>=(1-theta)||S||_2^2
   >=(1-theta)gamma/2-o(1),                           (NCPS3)
```

a contradiction.  Therefore `Gamma` is non-hyperlinear.
