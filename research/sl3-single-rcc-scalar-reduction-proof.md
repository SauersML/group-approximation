---
rg: 2
id: sl3-single-rcc-scalar-reduction-proof
kind: route
title: Identify the two-point seed with one commutator and telescope the D8 word
target: sl3-two-point-lamp-mark-is-single-rcc-scalar
requires: []
---

Because `c^2=1`, the pair lamp at `C,hC` is
`c h c h^-1=[c,h]`.  For any unitary `m,z` and scalar phase `lambda`,

```text
||m z m^-1 z^-1-I||_2 <= 2||m-lambda I||_2.
```

Minimize over `lambda` and use
`D(m)^2<=2(1-|tr(m)|^2)`.  Insert the D8 relator error to obtain
`(RCS3)--(RCS4)`.  Hence projective relative-commutant transfer for the single
actor word `h` collapses `J`.  This is a separate sufficient endpoint from
global all-pairs lamp rounding.
