---
rg: 2
id: finite-dyadic-torus-edge-neutrality-proof
kind: route
title: Use Walsh mutually unbiased towers and tensor the two-dimensional torus factorization
target: finite-dyadic-towers-are-neutral-with-one-torus-edge
requires:
  - unbalanced-torus-word-localizes-britton-leak
---

Put `d=2^R`, let `F_R=F^(tensor R)` for

```text
F=2^(-1/2)[[1,1],[1,-1]],
```

and index the computational basis by `0,...,d-1`.  With
`zeta=exp(2*pi*i/d)`, set

```text
T=diag(1,zeta,...,zeta^(d-1)),       H=F_R.             (FDP1)
```

Partition the spectrum into the consecutive dyadic arcs and let `q_(r,j)`
be the corresponding diagonal projection.  It has rank `d/2^r`, and the
partitions refine exactly.  Since every entry of `F_R` has squared modulus
`1/d`, any two diagonal projections `P,Q` satisfy

```text
tr_d(P F_R Q F_R^*)=rank(P)rank(Q)/d^2.                (FDP2)
```

Taking `P=q_(r,i)` and `Q=q_(s,j)` proves `(FDT1)`.

It remains to place the torus word on the same `R` tensor bits.  In `M_2`
put

```text
Z=diag(1,-1),        X=[[0,1],[1,0]],
D=diag(1,i),         E=exp(i*pi/4)Z.
```

At one bit use

```text
A_12=I,       W_12=iI,       B_21=iZ,
A_23=D,       W_23=E,        B_32=D.                   (FDP3)
```

All six matrices are diagonal.  Direct multiplication gives

```text
A_12(FB_21F)A_12W_12^*=X,
A_23(FB_32F)A_23W_23^*=FZ,
X(FZ)=F.                                                (FDP4)
```

For the `R`-bit packet take the `R`-fold tensor power of every coefficient
in `(FDP3)`.  Equation `(FDP4)` tensors, so the two torus factors multiply
to `F_R=H`; the unbalanced relator defect is zero.  Every coefficient stays
diagonal in the computational basis and hence commutes with the `T` of
`(FDP1)`.

The first cross-Gram is also exact.  Using the constant-modulus entries of
`F_R` and the fact that the complete root sum vanishes,

```text
tr_d(T^*F_R T F_R^*)
 =d^(-2)(sum_a conjugate(zeta)^a)(sum_b zeta^b)=0.      (FDP5)
```

Since `F_R=F_R^*`, this is `(FDT2)`.

Now all inputs of `unbalanced-torus-word-localizes-britton-leak` have
`eta_R=eta_L=eta_B=0`.  Its inequality `(UBL3)` therefore gives

```text
eta_21+eta_32>=sqrt(2),
```

which is `(FDT3)` and completes the proof.
