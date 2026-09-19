---
rg: 2
id: one-denominator-torus-dyadic-clock-proof
kind: route
title: Tensor the equality case of the Britton leak with a regular dyadic clock
target: britton-root-leak-bound-is-sharp-at-every-dyadic-depth
requires:
  - unbalanced-torus-and-swap-commutation-do-not-control-fold-square
  - unbalanced-torus-word-localizes-britton-leak
---

Let

```text
Z=[[1,0],[0,-1]],        X=[[0,1],[1,0]],
F=2^(-1/2)(X+Z),         D=diag(1,i),
zeta=exp(pi i/4).                                            (1)
```

As in `(USP1)`, put on the first factor

```text
H_0=F,
A_12=B_21=D,             W_12=Z,
A_23=zeta^(-1)Z,         B_32=I,       W_23=A_23.            (2)
```

These six matrices are diagonal.  The calculation `(USP2)--(USP3)` gives
the exact unbalanced closure

```text
ev_(A,B,W,H_0)(R_tor)=I.                                    (3)
```

Let `L_R` be the left regular generator of `C_(2^R)` and work on
`C^2 tensor l^2(C_(2^R))`.  Set

```text
T=Z tensor L_R,                  H=F tensor I,                 (4)
Y=Y_0 tensor I
```

for every displayed coefficient `Y_0` in `(2)`.  Every coefficient
commutes with `T`.  Since the second factor of `H` is the identity, `(3)`
continues to hold after tensoring.

The spectrum of `L_R` consists uniformly of all `2^R`-th roots of unity.
Multiplication by the two eigenvalues of `Z` only permutes this root set
(with doubled multiplicity), so `T` has exact order `2^R` and uniform
`2^R`-point spectrum.  Consecutive spectral blocks define `(ODC1)` and give
the trace and refinement identities `(ODC3)` exactly.  Equation `(ODC2)`
is literal conjugation by the same `H` occurring in `(3)`.

Because `F=F^*=F^(-1)` and `FZF=X`,

```text
T^*H^*TH=(ZX) tensor I.                                    (5)
```

The Pauli word `ZX` has trace zero, proving the last part of `(ODC5)`.

Finally `T_1=H^*TH=X tensor L_R`.  The clock cancels from conjugation of
the displayed coefficients.  Since `B_32=I`,

```text
eta_32=0.                                                  (6)
```

For `B_21=D`,

```text
XDX=diag(i,1),
||XDX-D||_2^2=2,                                          (7)
```

with normalized trace on `M_2`.  Hence `eta_21=sqrt(2)`.  The torus defect,
the base-coefficient commutator defects, and the first cross-Gram parameter
in `(UBL3)` are all zero, so its lower bound is `sqrt(2)` and `(6)--(7)`
attain equality.

The model is exact in every dimension `2^(R+1)`.  It need not have the full
mutually unbiased scalar overlap table supplied by the separate Walsh
packet; it instead proves equality in `(UBL3)`.  Its intentional omission
is the same as in the underlying Mach--Zehnder packet: the six displayed
coefficient slots do not form one representation of the full lattice.
Consequently the next usable relation must detect that omitted common-actor
consistency; increasing dyadic depth cannot improve the root-leak constant.
