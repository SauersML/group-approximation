---
rg: 2
id: titz-witzel-trivial-second-matching-proof
kind: route
title: Use the third and fourth coupling words to force the square of the arbitrary permutation to the identity
target: titz-witzel-trivial-second-matching-collapses-mark
requires:
  - titz-witzel-sofic-gate-has-only-seven-relators
---

Put `e=1` in `(TW8)`.  Then

```text
Y=r^2,                 X=r^(-4)c,
B'=F'=H'=1,
A'=r^(-4)c r^(-4),    D'=r^(-4)c r^(-2).                 (1)
```

The third and fourth coupling words therefore reduce respectively to

```text
A'D',                  D'.                               (2)
```

Write `delta_3=d_H(A'D',1)` and `delta_4=d_H(D',1)`.  Bi-invariance of
normalized Hamming distance first gives

```text
d_H(A',1) <= delta_3+delta_4.                            (3)
```

Multiplying `D'=r^(-4)c r^(-2)` on the left by `r^4` and on the right by
`r^2` gives

```text
d_H(c,r^6)=delta_4.                                     (4)
```

If `c` in the word `A'=r^(-4)c r^(-4)` is replaced by `r^6`, the result is
`r^(-2)`.  Another use of bi-invariance, followed by (3)--(4), yields

```text
d_H(r^2,1)=d_H(r^(-2),1)
            <= d_H(r^(-2),A')+d_H(A',1)
            <= delta_3+2 delta_4.                        (5)
```

Since `Y^8=r^16=(r^2)^8`, the Hamming telescoping inequality applied to
(5) proves

```text
d_H(Y^8,1)<=8d_H(r^2,1)<=8delta_3+16delta_4.
```

For an explicit version of the asymptotic extension, put
`beta=d_H(e,1)` and replace `e` by the identity while keeping `c,r` fixed.
After expanding the abbreviations in `(TW8)`, the third coupling word has
fourteen occurrences of `e^+-1`, the fourth has eleven, and `Y^8` has eight.
The fixed-word telescoping inequality therefore gives

```text
delta_3' <= delta_3+14 beta,
delta_4' <= delta_4+11 beta,
d_H(Y^8,(Y')^8) <= 8 beta.                               (6)
```

Apply `(TEM2)` to the primed triple.  Combining (6) gives

```text
d_H(Y^8,1)
 <=8(delta_3+14beta)+16(delta_4+11beta)+8beta
 =8delta_3+16delta_4+296beta,
```

which is `(TEM3)` and in particular proves the stated asymptotic conclusion.
