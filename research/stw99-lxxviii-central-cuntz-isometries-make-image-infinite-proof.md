---
rg: 2
id: stw99-lxxviii-central-cuntz-isometries-make-image-infinite-proof
kind: route
title: Compare two central orthogonal copies and descend from the sequence algebra
target: stw99-lxxviii-oinfinity-map-has-infinite-image
requires: []
---

Put `c=phi(a)`.  By `O_infinity`-stability, the relative commutant
`B_infinity cap phi(A)'` contains two isometries `s_1,s_2` with orthogonal
ranges.  They commute with `c`, and hence

```text
s_1 c s_1* + s_2 c s_2*
  <= c(s_1s_1*+s_2s_2*)
  <= c
```

inside `B_infinity`.  The two summands are orthogonal and each is Cuntz
equivalent to `c`, so

```text
c directSum c Cuntz-below c
```

in the sequence algebra.

It remains to check that no comparison was lost in the quotient.  Cuntz
subequivalence is witnessed by norm approximations: for every `epsilon>0`, a
matrix `x` over `B_infinity` satisfies

```text
||x* c x-(c directSum c-epsilon)_+|| < epsilon.
```

Represent `x` by a bounded sequence of matrices over `B`.  At some coordinate
the same inequality holds with `2 epsilon` in place of `epsilon`.  Since this
can be done for every `epsilon`, the standard cut-down characterization gives
`c directSum c Cuntz-below c` already in `B`.  Nonzero `c` is therefore
properly infinite.
