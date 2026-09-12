---
rg: 2
id: balanced-word-haar-small-ball
kind: claim
title: Balanced relators inherit dimension-uniform Haar small-ball bounds on U(n)
artifacts:
  - research/artifacts/random-relator-density-repair-2026-08-18.md
---

Fix `k>=2` and a finite nonempty set

```text
W subset [F_k,F_k] \ {1}.
```

There are constants `alpha,rho>0`, depending only on `W`, such that for every
`n>=2`, every `w in W`, and every normalized-Hilbert--Schmidt ball

```text
B_n(r)={V in SU(n): d_2(V,1)<=r},   0<r<=rho,
```

independent Haar `U_1,...,U_k in U(n)` satisfy

```text
Pr[ w(U_1,...,U_k) in B_n(r) ]
 <= Haar_SU(n)(B_n(r))^alpha.
```

Consequently, for any probability distribution `mu` on `W`, if

```text
p_(n,r)(U)=Pr_(w~mu)[d_2(w(U),1)<=r],
beta_n(r)=Haar_SU(n)(B_n(r)),
```

then

```text
Integral_(U(n)^k) p_(n,r)(U) dU <= beta_n(r)^alpha
```

and for every `q>0`,

```text
Haar{U:p_(n,r)(U)>=q} <= q^(-1) beta_n(r)^alpha.
```

The point of the balanced hypothesis is that it removes a real `SU/U`
compatibility problem: every `w in [F_k,F_k]` is unchanged when arbitrary
scalar phases multiply the generators, so Haar `U(n)` evaluation factors
through the `SU(n)` word distribution without determinant-normalizing the
microstate.
