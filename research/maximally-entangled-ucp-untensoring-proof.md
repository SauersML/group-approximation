---
rg: 2
id: maximally-entangled-ucp-untensoring-proof
kind: route
title: Tensor by an exact regular packet and recover through its invariant maximally entangled vector
target: residual-finite-regularization-removes-the-weak-ucp-quantifier
requires:
  - kazhdan-almost-invariant-corner-near-invariant-projection
---

Let `sigma:Gamma -> U(e)` be a genuine representation and let
`Psi:C^*(Gamma)->M_d tensor M_e` be ucp.  Write

```text
Omega=e^(-1/2) sum_(j=1)^e e_j tensor bar(e_j).
```

Then `(sigma(g) tensor bar(sigma(g)))Omega=Omega`.  With
`Delta(u_g)=u_g tensor u_g`, define

```text
Theta(x)
 =(I_d tensor <Omega|)
   ((Psi tensor bar(sigma))(Delta(x)))
   (I_d tensor |Omega>).                                (RUP1)
```

This is ucp: use a Stinespring dilation of `Psi`, tensor its genuine
representation with `bar(sigma)`, and compress by the isometry
`xi |-> xi tensor Omega`.  On group generators, invariance of `Omega` gives

```text
Theta(u_g)-alpha(g)
 =(id_d tensor tr_e)
   ((Psi(u_g)-alpha(g) tensor sigma(g))
       (I_d tensor sigma(g)^*)).                         (RUP2)
```

The normalized partial trace is the orthogonal projection in tracial
`L^2`, and right multiplication by `I tensor sigma(g)^*` is an isometry.
Therefore

```text
||Theta(u_g)-alpha(g)||_(2,d)
 <= ||Psi(u_g)-alpha(g) tensor sigma(g)||_(2,de).        (RUP3)
```

There is no factor depending on `e`; this constant-one estimate is the
load-bearing point.

Now let `alpha_n` be any asymptotic representation and let `sigma_n`
satisfy `(RUR1)`.  Exactness of `sigma_n` gives

```text
||beta_n(gh)-beta_n(g)beta_n(h)||_2
 =||alpha_n(gh)-alpha_n(g)alpha_n(h)||_2 ->0,
```

and

```text
tr(beta_n(g))=tr(alpha_n(g))tr(sigma_n(g))->0
```

for `g != e`.  Thus `beta_n` is hyperlinear.  Apply the hypothesized weak
ucp correction to `beta_n` and then `(RUP1)--(RUP3)` pointwise to recover
the required ucp correction of `alpha_n`.

For the Kazhdan corollary, start with any separating hyperlinear
approximation.  The established Kazhdan corner-rounding theorem replaces
its weak ucp dilation by genuine finite-dimensional representations
`sigma_n` on dimensions `e_n=(1+o(1))d_n`.  Their compressions are close to
the original tuple.  Hence, for `g != e`,

```text
|tr_(e_n)(sigma_n(g))|
 <= (d_n/e_n)|tr_(d_n)(phi_n(g))|+o(1)+(e_n-d_n)/e_n ->0.
```

They satisfy `(RUR1)`.  The first part now supplies ucp corrections for all
asymptotic representations, and a second application of Kazhdan corner
rounding makes those corrections flexible genuine representations.
