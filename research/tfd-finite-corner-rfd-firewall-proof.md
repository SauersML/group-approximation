---
rg: 2
id: tfd-finite-corner-rfd-firewall-proof
kind: route
title: Use spectral permanence for RFD and round every finite corner
target: tfd-finite-corner-collapse-and-rfd-firewall
requires:
  - tfd-low-leakage-compressions-flexibly-reduce
  - dv-s-arithmetic-hs-stable-nonhyperlinear-extension
  - finite-index-double-theorem-misses-iwahori-twist
---

Fix a finite symmetric generating set `S`. Put the positive Kazhdan
Laplacian

```text
Delta=sum_(s in S) (1-s)^*(1-s) in C^*(Gamma).          (1)
```

Property `(T;FD)` supplies `c>0` such that for every
finite-dimensional unitary representation `pi`,

```text
Spec(pi(Delta)) subset {0} union [c,infinity).           (2)
```

Indeed, the kernel is the invariant subspace and the uniform
finite-dimensional Kazhdan constant bounds `Delta` below on its
orthogonal complement.

Assume `C^*(Gamma)` is RFD. The product `Phi` of a set of
representatives of all finite-dimensional representations is a faithful
unital star homomorphism

```text
Phi:C^*(Gamma)->product_pi B(H_pi).                      (3)
```

For `0<lambda<c`, every coordinate
`pi(Delta)-lambda` is invertible, with the uniform bound

```text
||(pi(Delta)-lambda)^(-1)||
 <=max(lambda^(-1),(c-lambda)^(-1)).                    (4)
```

Thus `Phi(Delta)-lambda` is invertible in the product. A unital
C-star subalgebra is inverse closed in its ambient C-star algebra, and a
faithful star homomorphism is spectrally permanent. Hence

```text
Spec_(C^*(Gamma))(Delta) subset {0} union [c,infinity).  (5)
```

Every unitary representation of `Gamma` now has the same gap. An
almost-invariant unit vector forces `0` into the spectrum of its
Laplacian; since `0` is isolated by `(5)`, the spectral projection at
`0` is nonzero and supplies an invariant vector. This is property
`(T)`, proving the first assertion.

For the corner assertion, identify `C^(d_n)` with the range of
`P_n=V_nV_n^*` and write

```text
B_(n,s)=P_n pi_n(s) P_n|_(P_n C^(D_n)),
eta_n=max_(s in S)||B_(n,s)-phi_n(s)||_F/sqrt(d_n).      (6)
```

Then `eta_n->0`. Since `phi_n(s)` is unitary and `B_(n,s)` is a
contraction,

```text
||(1-P_n)pi_n(s)P_n||_F^2
 =d_n-||B_(n,s)||_F^2
 <=d_n(1-(1-eta_n)^2)
 <=2d_n eta_n.                                          (7)
```

Consequently the total leakage from
`tfd-low-leakage-compressions-flexibly-reduce` satisfies

```text
ell(P_n,pi_n)<=2|S| eta_n=o(1).                          (8)
```

Let `rho_n(s)` be a unitary polar completion of `B_(n,s)`. The
singular-value estimate used in that theorem also gives

```text
||rho_n(s)-B_(n,s)||_F^2
 <=||(1-P_n)pi_n(s)P_n||_F^2,                           (9)
```

so `rho_n(s)` is `o(1)` from `phi_n(s)` in normalized
Hilbert--Schmidt norm. Applying the low-leakage theorem to `P_n,pi_n`
produces an exact representation `sigma_n` on

```text
E_n>=d_n,        E_n/d_n-1=O(ell(P_n,pi_n))=o(1),       (10)
```

at generalized distance `O(sqrt(ell(P_n,pi_n)))` from `rho_n).
Equations `(6),(9),(10)` prove the second assertion.

The construction takes a `pi_n(Gamma)`-invariant subspace and, when
needed, adds trivial lines. Therefore a finite-quotient or congruence
factorization of `pi_n` is preserved.

Now take `Gamma=SL_2(Z[1/2])`. Dogon--Vigdorovich's arithmetic theorem
uses the Lubotzky--Zimmer property-`(T;FD)` gap for this group. On the
other hand `Gamma` is an infinite a-T-menable lattice and is not
property `(T)`; Fournier-Facio--Willett also record this exact
`(T;FD)`-but-not-`(T)` example in arXiv:2603.18456v2, immediately
after Question 1.8. The first part therefore proves that its full group
C-star algebra is not RFD.

Fournier-Facio--Willett, Theorem 7.11, first uses LLP to lift the prescribed
quotient homomorphism only to ucp maps. It then uses Fell density of a
chosen representation family--RFD for all finite-dimensional
representations, or FD for finite-quotient representations--to obtain
finite-dimensional exact corners. The required RFD hypothesis is
impossible here, while the LLP step alone may have infinite-dimensional
Stinespring dilations and lies outside property `(T;FD)`.

Finally, Shulman, arXiv:2603.13564, Theorem 10 treats the identity double
`A *_C A`. By
`finite-index-double-theorem-misses-iwahori-twist`, the Iwahori edge
commensuration does not extend to a modular-vertex automorphism, so this is
not that double. Her Theorem 20 is an existence criterion for an MF
embedding from compatible norm-ultraproduct embeddings. Neither theorem
turns an arbitrary prescribed tracial-ultraproduct homomorphism into
coordinate exact representations. That missing relative selection is
exactly the union-basin lift.
