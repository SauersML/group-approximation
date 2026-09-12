---
rg: 2
id: binary-jacobson-tail-phase-cannot-correct-closing-fold
kind: claim
title: The Jacobson tail sign exactly switches the closing fold from degree four to degree two, and spectral phases cannot repair it
artifacts:
  - research/binary-jacobson-tail-phase-fold-proof.md
distinct_from:
  binary-jacobson-closing-root-folds-head-two-to-one: that constructs the two-to-one coisometry and isolates the tail-center as the sole relative branch gauge; this computes the complete folded native packet on both tail signs and rules out every correction taken only from that center.
  binary-jacobson-balanced-split-conserves-pauli-parity: that computes the two coefficient branches of one balanced conjugation before the closing root is used; this treats the actual coisometric closing fold and its literal native four-tuple.
  binary-jacobson-raw-cycle-selects-common-pi-intertwiner: that asks for a same-occurrence return from a degree-two source to the literal degree-four target; this supplies the degree-two folded tuple canonically but not the square return inside its raw range.
---

**ESTABLISHED.**  Use the notation of
`binary-jacobson-closing-root-folds-head-two-to-one` and write

```text
P=(1-rho(x_13(Q)))/2,       Y=rho(x_23(Q)),
E_-=P(1-Y)/2,               E_+=P(1+Y)/2,
R^*R=E_-,                   RR^*=F,
b=rho(x_12(1)),             c=rho(x_13(ST)).             (JTP1)
```

The tail-center `c` commutes with `P,Y,b` and with all four native packet
words

```text
D=(X_0,Z_0,X_1,Z_1)
 =(x_12(Q),x_23(1),x_14(Q),x_43(1)).                    (JTP2)
```

Let `phi` be any unitary in the two-dimensional spectral algebra generated
by `c`, and form the phase-corrected closing fold

```text
T_phi=2^(-1/2) R(1+b phi).                              (JTP3)
```

Then `T_phi T_phi^*=F` for **every** such phase.  Put

```text
P_epsilon=P(1+epsilon c)/2,
F_epsilon=R E_- P_epsilon R^*,        epsilon in {+1,-1}.
                                                                    (JTP4)
```

Whenever `P_epsilon` is nonzero, `F_epsilon` is nonzero and

```text
rank(F_epsilon)=rank(P_epsilon)/2.                      (JTP5)
```

On `F_epsilon`, compression through the same fold gives

```text
T_phi Z_0 T_phi^* = ((1-epsilon)/2) R Z_0 R^*,
T_phi X_1 T_phi^* = R X_1 R^*,
T_phi Z_1 T_phi^* = R Z_1 R^*.                          (JTP6)
```

In particular the `Z_0` row is independent of `phi`.  On the positive tail
cut it is identically zero, while the last pair remains Pauli.  Hence the
folded four-tuple on every nonzero `F_+` belongs to a quotient of

```text
M_2(C) directSum M_2(C)
```

and satisfies the degree-four standard identity `s_4=0`.  If `phi` is a
self-adjoint spectral phase, the folded `X_0` row is a signed involution
commuting with that `M_2` factor, so this degree-two description is exact.

On the negative tail cut, `Z_0` survives.  For a self-adjoint spectral phase
the two folded Pauli pairs remain transverse and the tuple has the native
degree-four algebra `M_4 tensor I`.

Thus the sought degree drop is already selected by the literal closing fold:

```text
c=+1  ==>  folded PI degree at most two,
c=-1  ==>  folded PI degree four.                        (JTP7)
```

But no scalar, sign, or general unitary phase obtained from the spectrum of
`x_13(ST)` can restore the erased `Z_0` occurrence on the positive tail cut.
The remaining opposite root must act through a genuinely noncentral
incidence with the raw range `F`; a tail spectral correction alone cannot
authenticate the literal `M_4` target there.

DERIVATION
binary-jacobson-tail-phase-fold-proof
