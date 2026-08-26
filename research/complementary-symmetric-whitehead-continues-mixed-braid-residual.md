---
rg: 2
id: complementary-symmetric-whitehead-continues-mixed-braid-residual
kind: route
title: Continue the mixed-braid residual with its complementary symmetric Whitehead
target: el20-six-moving-coefficient-square-bridges
requires:
  - mixed-braid-gauge-cancellation-misses-signed-hecke-targets
---

**INVALIDATED COMPLEMENTARY IDENTIFICATION.**  Replace the asymmetric
residual

```text
P=x_79(q_1)x_97(q_1)x_79(1)
```

by the superficially similar symmetric word

```text
A=x_79(1)x_97(q_1)x_79(1)
```

and braid it with the complementary `q_0` word.  The latter words do close
to the two support Whiteheads, but
`complementary-mixed-braid-returns-support-but-retains-s3` proves that
`A!=P`.  Thus this support-cell calculation does not continue the actual
mixed-braid residual.
