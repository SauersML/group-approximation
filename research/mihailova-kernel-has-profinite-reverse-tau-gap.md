---
rg: 2
id: mihailova-kernel-has-profinite-reverse-tau-gap
kind: claim
title: The profinitely dense Mihailova kernel contains a finite reverse-Kazhdan set for every finite-image SL3 representation
distinct_from:
  sln-z-thin-codense-tau-pair: that constructs an external finitely generated thin profinitely dense subgroup of SL_n(Z); this extracts such a subgroup inside the prescribed infinitely generated Mihailova kernel N and uses its gap to exclude one coset coefficient.
  orbitwise-relator-classicalization-separates-mihailova-kernel: that assumes exact finite branches and concludes subgroup separability; this is a uniform spectral statement about approximate N-invariance in finite-image representations and invokes no finite-index subgroup containing N.
  fd-fell-coset-observable-gaussianizes-wreath: that proves hyperlinearity from finite-image Fell approximation of 1_N; this refutes that approximation for the actual ambient arithmetic N.
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

Let

```text
E=F_m < L=SL_3(Z),       N=ker(E->Q),                  (PRT1)
```

where `E` is profinitely dense in `L` and `Q` is nontrivial and has no
nontrivial finite quotients.  Then there are a finite symmetric set `S<N`
and `kappa>0` such that for every finite-image unitary representation
`rho:L->U(V)`, with `P_rho` the projection onto `V^L`,

```text
||v-P_rho v|| <= kappa^(-1) max_(s in S)||rho(s)v-v||. (PRT2)
```

Consequently the Mihailova coset coefficient is not a finite-image Fell
limit:

```text
1_N notin closure_pointwise {
  g |-> <rho(g)xi,xi> : rho finite-image, ||xi||=1
}.                                                       (PRT3)
```

Equivalently, if `Lhat` is the profinite completion and `pi_pf` is the direct
sum of all continuous finite-dimensional representations of `Lhat`, then

```text
lambda_(L/N) is not weakly contained in pi_pf|_L.       (PRT4)
```

This is the exact compact/profinite representation criterion behind
`fd-fell-coset-observable-gaussianizes-wreath`: pointwise finite-image
coefficient approximation is precisely weak containment of the cyclic
quasi-regular representation in the profinite Peter--Weyl representation.
For the actual `N`, `(PRT2)` refutes it quantitatively.

Thus the Gaussian Fell construction cannot make the isolated coset wreath
hyperlinear.  This does not decide the wreath's hyperlinearity: arbitrary HS
microstates need not lift to exact finite-image actor representations, and a
non-Gaussian/non-Fell model remains logically possible.

