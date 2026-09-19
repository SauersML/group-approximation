---
rg: 2
id: cyclic-aperiodicity-collapses-two-actor-grade-unitaries
kind: claim
title: Cyclic aperiodicity collapses every two-actor-grade unitary to one grade
distinct_from:
  centralizer-aperiodic-haar-actor-marginals-force-regular-trace: that uses centralizer orbits to authenticate mixed traces; this uses the stronger cyclic aperiodicity condition to classify exact two-grade unitaries algebraically.
  manzoor-irs-generators-cannot-be-single-actor-grade: that obstructs an injective homogeneous placement by a positive IRS word trace; this proves that allowing one additional actor grade gives no additional freedom on the aperiodic algebraic base.
  finite-one-hot-algebraic-corners-reduce-to-stabilizers: that decomposes a finite invariant selector corner into matrix algebras over stabilizers; this treats arbitrary measurable Fourier coefficients in an ergodic infinite algebraic action.
---

Let a torsion-free group `H` act by automorphisms on a countable discrete
abelian group `A`, put `K=dual(A)`, and assume the cyclic aperiodicity condition

```text
ker(r^n-1:A->A)={0}       for every r!=e and n>=1.     (CAT1)
```

Equivalently, every nonidentity `r in H` acts ergodically on `(K,Haar)`.
In the canonical crossed product

```text
M=L^infinity(K) rtimes H,
```

let a unitary have actor Fourier support of size at most two:

```text
X=a U_g+b U_h,                 a,b in L^infinity(K).   (CAT2)
```

Then one coefficient vanishes. More precisely, if `g!=h`, there is a
projection `p in L^infinity(K)` and unimodular measurable coefficients on
their supports such that

```text
|a|^2=p,       |b|^2=1-p,       alpha_(h g^(-1))(p)=p. (CAT3)
```

Ergodicity in `(CAT1)` forces `p=0` or `p=1`. Hence every unitary with at most
two actor grades is homogeneous:

```text
X=B U_r                    for some B in U(L^infinity(K)), r in H. (CAT4)
```

Thus a cyclic-aperiodic algebraic envelope has no genuine two-grade Fourier
seam. The boundary is sharp: `three-actor-grades-support-an-exact-hadamard-cell`
constructs a three-grade self-adjoint unitary which does not even normalize
the abelian base. That local cell does not yet supply the required Manzoor
moments or multiplication law.
---
