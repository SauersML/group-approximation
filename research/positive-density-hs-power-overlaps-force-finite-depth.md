---
rg: 2
id: positive-density-hs-power-overlaps-force-finite-depth
kind: claim
title: Geometrically small Hilbert--Schmidt power overlaps already force finite depth
distinct_from:
  positive-density-power-dilation-forces-finite-depth: that assumes coherent operator compressions and obtains an injective orbit frame; this needs only scalar Hilbert--Schmidt overlaps and uses the rank--frame-potential inequality.
  summable-power-return-detectors-miss-growing-cycles: that lets the tested density or detected scale escape along a sequence; this fixes one positive density and one finite list of powers before taking the microstate limit.
  canonical-positive-density-no-return-dilation-tail: that asks for the stronger identities `qu^nq=T^n`; this proves that finitely many geometric overlap bounds are already sufficient for the Culf--Mastel capacity contradiction.
---

Let `H` have dimension `d`, let `Q` be a projection of normalized rank
`alpha=rank(Q)/d`, and let `U` be unitary.  Fix `0<=rho<1` and integers
`N,L>=1`.  If

```text
||Q U^(kL) Q||_(2,H)^2 <= alpha rho^(2kL),
                                      1<=k<=N,          (HPO1)
```

where `||X||_(2,H)^2=d^(-1)Tr(X^*X)`, then

```text
(N+1)alpha
 <= 1+2 sum_(k=1)^N (1-k/(N+1))rho^(2kL)
 <= 1+2 rho^(2L)/(1-rho^(2L)).                         (HPO2)
```

The same conclusion holds asymptotically if `(HPO1)` has an additive
`o(1)` error at each of the finitely many fixed powers and
`tr_H(Q)->alpha`.

Consequently, for every fixed `alpha>0` and `rho<1`, choose `N,L`
computably so that

```text
(N+1)alpha
 >1+2 rho^(2L)/(1-rho^(2L)).                           (HPO3)
```

No canonical-profile matrix microstate sequence can then satisfy the finite
overlap list `(HPO1)`.  In particular one does not need the operator
identities `QU^nQ=T^n`: it is enough to return the scalar overlaps of powers
at the sampled times `L,2L,...,NL`.

This weakening is important for controller orientation.  Left or right
multiplication of a returned block by an arbitrary multiplicity unitary
does not change its Hilbert--Schmidt norm.  It does not, however, make a
finite controller into a tail: the exact return in
`finite-cocycle-select-has-an-exact-power-return` has
`||qC^2q||_(2,q)=1`, so it violates `(HPO1)` maximally at the second power.

