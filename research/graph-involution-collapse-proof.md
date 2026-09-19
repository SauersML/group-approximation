---
rg: 2
id: graph-involution-collapse-proof
kind: route
title: Convert graph involutivity to a two-projection spectral contradiction
target: graph-involution-forces-paz-return
requires: []
---

Use the graph notation `R,U,S=2R-I` and write the first diagonal block of
the commutator as

```text
C_1=S U^* S U=ST,  T=U^*SU.
```

If `C` is self-adjoint, then `ST=(ST)^*=TS`; hence the projections
`R` and `R'=U^*RU` commute and `K=RR'R` is a projection.  Identify `GH`
isometrically with `RH` by `xi -> 2^(-1/2)(xi,xi)`.  Under this
identification,

```text
K corresponds to H^*H,  H=G(I+W)G/2.
```

The compression bound gives `||H||_op<=(1+rho)/2<1`, whereas the reverse
triangle inequality gives `||Hxi||>=(1-rho)||xi||/2` on `GH`.  Since
`H^*H` is a projection of norm strictly below one it is zero; the lower
bound then forces `GH=0`.

For the quantitative form let `epsilon=||C-Y||_2`, where `Y=Y^*` and
`Y^2=I`.  Then `||C-C^*||_2<=2epsilon`, which on the first block gives
`||[R,R']||_2<=epsilon` up to the fixed block normalization.  The standard
two-projection identity yields

```text
tau_2(K-K^2)<=epsilon^2/2.                              (1)
```

With `a=(1+rho)/2`, `b=(1-rho)/2`, the graph compression satisfies
`b^2R<=K<=a^2R`.  Therefore

```text
(1-a^2)tau_2(K)<=tau_2(K-K^2),
tau_2(K)>=b^2 tau(G)/2.
```

Combining these inequalities with `(1)` gives the displayed bound.  Fixed
spectral rounding adds only the corresponding involution defect when `Y`
is initially approximate.
