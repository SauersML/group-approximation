---
rg: 2
id: full-arithmetic-bernoulli-projection-orbit-is-free-spherical
kind: claim
title: The full arithmetic Bernoulli projection orbit is the free spherical point
distinct_from:
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that gives a conditional matrix-ultraproduct counterexample if the crossed product is Connes embeddable; the present statement is an unconditional exact calculation of every joint projection-orbit moment and only fences dimension-blind scalar recurrences.
  source-hecke-data-leave-projective-square-free: that varies one unitary coefficient while holding the source Hecke tower fixed; the present packet is a balanced projection whose entire covariant Boolean orbit has explicit joint moments.
  finite-affine-sl3-root-shell-keeps-interior-overlap: that is a genuine finite-matrix countermodel for a truncated root packet but fails dyadic transport; the present model satisfies the full arithmetic actor exactly but is not asserted to be Connes embeddable.
---

Let `C<A` be any proper subgroup pair and consider the binary generalized
Bernoulli crossed product

```text
N=L^infinity({0,1}^(A/C)) rtimes A.
```

Let `P` be the indicator of value `1` at the base coordinate `C`, and put

```text
P_(gC)=u_g P u_g^*.
```

This is well defined, `P` has trace `1/2`, and `P` commutes with the
canonical copy of `C`.  For any finite list `g_1,...,g_m`, if exactly `k`
distinct right cosets occur among `g_i C`, then

```text
tau(product_(i=1)^m P_(g_i C))=2^(-k).                    (FBP1)
```

In particular, with `Z_g=2P_(gC)-I`,

```text
tau(Z_g Z_l)=1_(gC=lC).                                  (FBP2)
```

Thus the centered projection orbit is an orthonormal copy of
`ell^2(A/C)`, and its normalized spherical coefficient is exactly

```text
phi(g)=1_C(g).                                           (FBP3)
```

For the arithmetic pair

```text
C=SL_3(Z) < A=SL_3(Z[1/2]),
```

every elementary, Steinberg, Weyl, dyadic-denominator, and Iwahori word
relation holds exactly in `N`, because the actor is the genuine canonical
copy of `A`.  Nevertheless, for
`h=diag(2,1,1/2)` and `Q=u_h P u_h^*`,

```text
tau(PQ)=1/4,
D=O=1/2,
1-|tau([(I-2P),u_h])|^2=1.                              (FBP4)
```

Consequently no scalar overlap recurrence which is a dimension-blind
tracial consequence of the actual arithmetic word relations can prove the
balanced-projection endpoint transfer.  This includes every recurrence
obtained only from positive definiteness of the spherical coefficient,
finite Hecke convolution identities, or arbitrary finite joint moments of
the covariant projection orbit: `(FBP1)` supplies a simultaneous exact
solution to all of them at the forbidden overlap.

The conclusion is a no-go, not a counterexample to projective transfer.
Turning this exact packet into matrices is exactly the unresolved Connes-
embeddability/relative-embeddability question for the generalized coset
Bernoulli crossed product.  A successful scalar-looking inequality must
therefore contain a premise that is genuinely special to matricial
microstates and is false or unavailable in `N`; adding further literal
elementary-matrix relations cannot suffice.

