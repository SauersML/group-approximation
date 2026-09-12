---
rg: 2
id: relative-induced-selector-has-intertwiner-order-dual
kind: claim
title: The arbitrary-core induced selector has an exact intertwiner-order dual
distinct_from:
  every-relative-ucp-window-lives-in-one-induced-representation: that parametrizes relative ucp maps by isometries in one induced host; this convexifies that parametrization and computes its exact finite order dual.
  relative-induced-selector-gap-has-bounded-dual-witness: that expresses the support function as a Choi SDP on the whole finite group algebra; this eliminates those Choi variables in favor of the core-intertwiner module and its right order.
  regular-hecke-kraus-support-has-exact-order-dual: that gives the regular-core commutant formula; this proves the arbitrary prescribed-core version from which the regular formula is a specialization.
---

Let `G` be finite, `B<G`, and let

```text
beta:B->U(H_beta),       dim(H_beta)=d,
rho=Ind_B^G(beta),       X_0=rho(x)=X_0*=X_0^(-1)
```

for an involution `x in G`. Define

```text
D_beta=beta(B)',
E_beta=Hom_B(H_beta,H_rho).                             (IOD1)
```

Give `E_beta` the normalized Hilbert--Schmidt inner product

```text
<V,W>=tr_d(V*W),
```

and let `P_E` be the orthogonal projection onto `E_beta`. For
`Y=Y* in B(H_beta)` and `Z=Z* in D_beta`, define

```text
T_Y(V)=P_E(X_0 V Y),
R_Z(V)=V Z.                                             (IOD2)
```

Both are selfadjoint operators on the finite Hilbert space `E_beta`.

Let `K_(G,B,beta,x)` be the set of all possible `x`-coefficients

```text
Theta(u_x),
```

where `Theta:C*(G)->B(H_beta)` is ucp and
`Theta(u_b)=beta(b)` for every `b in B`. Then

```text
h_beta(Y):=sup_(C in K) tr_d(YC)
 =min {tr_d(Z): Z=Z* in D_beta, R_Z>=T_Y}.             (IOD3)
```

Consequently, for every selfadjoint target `X`,

```text
Delta_(G,B,beta)(X)
 =max {tr_d(YX)-tr_d(Z):
       Y=Y*, Z=Z*, ||Y||_(2,d)<=1, R_Z>=T_Y}.          (IOD4)
```

The order inequality in (IOD3)--(IOD4) is a single linear matrix
inequality of size `dim_C(E_beta)`. Thus the exact relative selector for
an arbitrary authenticated core is a finite SDP entirely inside the
induced intertwiner module. Any feasible `(Y,Z)` is a certified
complete-order lower bound; primal intertwiner frames give upper bounds.

For a moving Iwahori level take

```text
G=A_N,       B=B_N,       beta=beta_N.
```

The surviving lift gate is therefore equivalent to showing that (IOD4)
tends to zero for the supplied matrices, or to excluding bounded
positive-gap order certificates on the moving modules `E_(beta_N)`.
LLP, MF, local reflexivity, and modular Fejer--Riesz factorization do not
estimate this module order uniformly. The nonhyperlinear-group root
remains open.

DERIVATION
relative-induced-intertwiner-order-dual-proof
