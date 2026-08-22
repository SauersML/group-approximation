---
rg: 2
id: transverse-companion-defects-pay-one-kill-completeness
kind: claim
title: Transverse companion defects pay one but destroy exact completeness
distinct_from:
  transverse-d8-two-swap-corner-unitarity-collapses-to-one-path: that analyzes one transverse return; this pairs it with the phase-rotated companion and proves the exact conservation law.
  binary-schur-toeplitz-one-branch-hs-payment: that needs an oriented paid exit compatible with an exact marked model; this gives only symmetric aggregate payment and identifies the selector escape.
---

# Transverse companion defects pay one but destroy exact completeness

ESTABLISHED. Keep the notation of
`transverse-d8-two-swap-corner-unitarity-collapses-to-one-path`:

```text
S=(W+W^*)/2,       T=(W-W^*)/2,
C_T=T U.                                                   (TCD1)
```

Phase-rotate the X-basis swap gauge from `W` to `iW`. Its skew part is

```text
(iW-(iW)^*)/2=i(W+W^*)/2=iS,
```

so, up to the harmless scalar `i`, the companion corner return is

```text
C_S=S U.                                                   (TCD2)
```

This companion is algebraic over complex group rings. If a literal packet
phase is desired, tensor the `D_8` type with the faithful character of a
central `C_4`; its generator supplies the scalar `i`.

Because `S` and `T` are the real and skew parts of one unitary,

```text
S^2+T^*T=I.                                                (TCD3)
```

Define the positive corner-unitarity deficits

```text
D_T=I-C_T^*C_T=U^*S^2U,
D_S=I-C_S^*C_S=U^*T^*TU.                                  (TCD4)
```

They satisfy the exact common-carrier conservation law

```text
D_T+D_S=I.                                                 (TCD5)
```

Consequently, for the normalized trace on the multiplicity carrier,

```text
(1-||C_T||_2^2)+(1-||C_S||_2^2)=1,                        (TCD6)
||D_T||_2^2+||D_S||_2^2 >= 1/2.                           (TCD7)
```

The second inequality is the pointwise bound
`x^2+(1-x)^2>=1/2` applied to `x=S^2`.

Thus the two branches cannot both have small unitary defect on the same
multiplicity mass, even after arbitrary direct-sum decomposition. This is an
exact dimension-independent aggregate HS payment.

It cannot be imposed as two exact group-algebra corner-unitarity relations
while preserving a nonzero marked carrier: `(TCD5)` says `D_T=D_S=0` would
force `I=0`. Hence the strongest common-carrier implementation destroys
completeness, not merely finite-dimensional approximability.

Allowing a branch selector restores an exact stationary escape. Decompose

```text
M=M_T direct_sum M_S,
W=iI on M_T,              W=I on M_S.                     (TCD8)
```

On `M_T`, `C_T` is unitary and `C_S=0`; on `M_S`, `C_S` is unitary and
`C_T=0`. A commuting selector `E=1_(M_T)` makes

```text
C_selected=E C_T+(1-E)C_S                                (TCD9)
```

unitary on all of `M`. Therefore any local rule saying that one of the two
branches may continue lets multiplicity choose the good branch sector by
sector. Direct sums do not reduce the aggregate payment `(TCD7)`, but they
completely defeat an oriented one-exit recurrence.

The exact implication is sharp. To use `(TCD7)` in a nonhyperlinearity
construction, the two corrected returns must arise only in finite-matrix
microstates on one canonically localized carrier, while the exact marked
representation is not required to satisfy both corner unitarities. Or an
external incidence must pin the selector independently of `W`; doing this is
the common-corner/holonomy problem, not a consequence of the two-cell
algebra. The companion identity solves analytic payment but exposes the
completeness and selector gates exactly.
