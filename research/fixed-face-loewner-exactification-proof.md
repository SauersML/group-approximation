---
rg: 2
id: fixed-face-loewner-exactification-proof
kind: route
title: Sequentially pinch, sign, and close the parity product
target: fixed-parity-faces-exactify-with-loewner-row-square-control
requires:
  - common-cut-contraction-sign-has-complete-balanced-energy-ledger
  - normalized-occurrence-equality-transfer-preserves-face-gap
---

For a selfadjoint contraction `X`, functional calculus gives

```text
 (X-sgn(X))^2<=(I-X^2),                                (LFEP1)
```

so the initial signing is paid by the first term of `(LFE1)`.

Now let `B` be a reflection and let `E` be the trace-preserving conditional
expectation onto the commutant of already installed commuting reflections.
Put `Y=E(B)`, `O=B-Y`, and `S=sgn(Y)`.  Conditional-expectation bimodularity
and `B^2=I` give

```text
 I-Y^2=E(O^2),        (Y-S)^2<=I-Y^2.
```

The operator square inequality `(u+v)^*(u+v)<=2u^*u+2v^*v` therefore gives

```text
 (B-S)^2<=2O^2+2E(O^2).                               (LFEP2)
```

Since `O=|G|^(-1)sum_g(B-gBg)`, operator Jensen bounds `O^2` by the
average squares of `B-gBg`.  Telescope each group word `g` through the at
most `q` installed reflections and apply the same square inequality.  This
bounds `(LFEP2)` by a fixed sum of conjugates of
`[B,A_j]^*[B,A_j]`.

At stage `r`, replace each installed `A_j` in these commutators by the
original signed coordinate plus its previous correction.  Expanding once
more bounds the new terms by the original commutator squares and finite
word conjugates of the earlier correction squares.  Induction terminates
after at most `q` stages and yields a constant depending only on `q`.

Finally compare the last original reflection with
`epsilon product_(i<m)S_i`.  Insert the product of the original signed
coordinates.  The first difference is a unitary translate of the parity
residual; telescope the second through the previous corrections.  Another
fixed-width square inequality proves `(LFE2)`.  Weighted summation and
bounded occurrence prove `(LFE3)`.
