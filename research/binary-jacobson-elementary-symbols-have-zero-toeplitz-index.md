---
rg: 2
id: binary-jacobson-elementary-symbols-have-zero-toeplitz-index
kind: claim
title: Every elementary Laurent symbol has zero Toeplitz index, so the head is not a K-one boundary obstruction
distinct_from:
  binary-jacobson-monomial-symbol-preimage-is-marked-mf: that constructs a marked MF model for the full monomial-symbol preimage; this proves directly that the algebraic Toeplitz index vanishes on the entire elementary Laurent quotient, including nonmonomial symbols.
  binary-jacobson-head-root-has-opnorm-square-decoder: that asks for a representation-dependent same-square decoder from the full group relations; this rules out replacing that decoder by the ordinary determinant/index boundary map.
---

**ESTABLISHED.**  Put

```text
J=F_2<S,T | TS=1>,       Q=1-ST,
A=F_2[z,z^(-1)],         mu:J->A,
mu(S)=z,                 mu(T)=z^(-1).
```

For a Laurent matrix `g in GL_m(A)`, define its total Toeplitz index by

```text
ind(g)=deg(det(g)) in Z,                                 (BTI1)
```

where `deg:A^x->Z` sends `z^k` to `k`.  Then

```text
ind(g)=0                    for every g in EL_m(A).       (BTI2)
```

Consequently the symbol of every element of `EL_5(J)` has zero ordinary
Toeplitz index.  In particular the head transvection

```text
x_13(Q) in ker(EL_5(J)->EL_5(A))                         (BTI3)
```

cannot be detected by the `K_1(A)->K_0(M_infinity(F_2))` boundary class of
the one-sided shift.  The unbalanced scalar symbol `z` has index one, but it
does not occur in the determinant-one elementary quotient.  Thus any
Property-`(T)`-free collapse of the Jacobson head must use nonabelian
extension/occurrence data, not the determinant, the balanced Whitehead lift,
or the ordinary algebraic Toeplitz index.
