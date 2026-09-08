---
rg: 2
id: central-c3-block-elimination-proves-direct-finiteness-equivalence
kind: route
title: Split cyclic parity and eliminate two blocks to obtain the full central three-cycle equivalence
target: central-c3-quadratic-surjunctivity-iff-direct-finiteness
requires: []
artifacts:
  - research/artifacts/gottschalk-central-odd-norm-conjugacy-direct-finiteness-2026-09-08.md
---

Put T=R_t, E=I+T+T^2, and Q_t(x)=xTx. Write x=d+c with Ed=0
and c=Ex. For N(d)=EQ_t(d), checking the four even-parity triples
gives (I-E)Q_t(d)=T^2d and N(d)d=d. The local involution
Psi(d,m)=(d,m+N(d)) therefore satisfies

    Q_t Psi(d,m)=m+mT^2d.

Since t is central, A preserves im E and ker E. Write its restrictions
as A_0 and A_1. The input change P=F Psi has the exact form

    P(d,m)=(L_m d,N(d)+B_0m),
    L_m d=d+A_1(mT^2d),       B_0=I+A_0.

Injectivity of P implies injectivity of the scalar linear rule B_0.
Direct finiteness makes B_0 bijective by scalar linear duality.
Every L_m is then injective, since any nonzero kernel vector would
collide with a point on the zero-d fiber. As L_0=I, finite-output
perturbations and compactness show that J(d,m)=(L_m d,m) is bijective.

The local map D=P J^-1 preserves d and has zero-d fiber B_0.
For finitely supported d, its m fiber is an injective finite-output
perturbation of B_0 and hence bijective. Density and compactness
give surjectivity of D, P, and F. No homogeneity of the second output
is needed.

Conversely, take A=(B-I)E for arbitrary scalar linear B on Gamma.
The same involution conjugates F to identity on ker E and B on im E.
Surjunctivity of all these F therefore implies scalar linear
surjunctivity on Gamma, equivalent to direct finiteness of F_2[Gamma].
