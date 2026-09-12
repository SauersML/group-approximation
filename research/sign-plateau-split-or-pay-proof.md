---
rg: 2
id: sign-plateau-split-or-pay-proof
kind: route
title: Average the plateau projection over the Weyl involution and round spectrally
target: sign-plateau-involution-split-or-pay
requires: []
---

Since `c^2=x^2=1`, unitary invariance gives

```text
||(c x)^2-1||_2
 =||c x c x-c^2||_2
 =||x c x-c||_2
 =2||x P x-P||_2
 =2||[P,x]||_2,
```

which is `(SPI1)`.

Set

```text
A=(P+x P x)/2.
```

Then `A` is a positive contraction commuting with `x`, and

```text
||P-A||_2=(1/2)||P-xPx||_2=(1/2)||[P,x]||_2.
```

Let `Q=1_([1/2,1])(A)`.  It commutes with `x`.  Spectral rounding gives
`||A-Q||_2<=||A-P||_2`, because `Q` is a nearest projection to the positive
contraction `A` in Hilbert--Schmidt norm.  The triangle inequality proves
`(SPI2)`.  Finally

```text
||[Q,g]||_2
 <=||[P,g]||_2+||[(Q-P),g]||_2
 <=||[P,g]||_2+2||Q-P||_2,
```

which is `(SPI3)`.

