---
rg: 2
id: iwahori-bs14-presentation-proof
kind: route
title: Eliminate the second modular involution and recover it by a reversible Tietze move
target: iwahori-square-root-presentation-is-bs14-plus-one-involution
requires:
  - iwahori-question-as-square-root-of-parabolic
---

Start from the exact square-root coordinates

```text
s^2=xy,  e^2=1,  (es)^3=1,
xy^2xyx=s^2ese,
x^2=1,  y^3=1.
```

Put `r=xe`, so `e=xr`, and use `y=xs^2`.  The fixed word identity

```text
xy^2xyx=s^2 x s^4 x
```

turns the last gluing equation into `ese=xs^4x`; conjugating by `x` gives
`rsr^(-1)=s^4`.  The remaining relations become, respectively,

```text
x^2=1,
(xr)^2=1,
(xs^2)^3=1,
(xrs)^3=1.
```

Conversely, from these five relations set `e=xr` and `y=xs^2`.  Then
`e^2=y^3=(es)^3=1`, while `rsr^(-1)=s^4` gives
`ese=xs^4x`; multiplying by `s^2` and reversing the displayed word identity
recovers the original gluing equation.  Both substitutions are inverse
Tietze transformations, proving the presentation claim.
