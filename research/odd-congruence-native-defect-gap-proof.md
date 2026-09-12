---
rg: 2
id: odd-congruence-native-defect-gap-proof
kind: route
title: Tensor-amplify a failed odd-congruence lamp inequality into a forbidden exact-sector leak
target: odd-congruence-native-sector-has-defect-only-gap
requires:
  - odd-congruence-lambda-exact-sector-collapses
---

Suppose no constant in `(ONG1)` exists.  For every `n` choose an assignment
`rho_n` and a balanced involution `c_n` in the stated exact odd-congruence
sector such that, writing

```text
epsilon_n=d_cc(rho_n,c_n),       e_n=e_h(rho_n,c_n),
```

one has

```text
e_n>n epsilon_n.                                        (ONP1)
```

Put `k_n=ceil(1/e_n)` and take diagonal tensor powers

```text
rho_tilde_n=rho_n^(tensor k_n),
c_tilde_n=c_n^(tensor k_n).                             (ONP2)
```

Word telescoping for tensor products gives

```text
d_cc(rho_tilde_n,c_tilde_n)
 <= k_n epsilon_n <=2/n.                               (ONP3)
```

The restriction of `rho_tilde_n` to `Lambda` is still an exact
representation factoring through the same odd congruence quotient.  The
tensor power of a self-adjoint involution is again a self-adjoint
involution, and its trace is zero because `tr(c_n)=0`.

If

```text
w_n=c_n rho_n(h)c_n rho_n(h)^*,
```

then the target word of the amplified tuple is `w_n^(tensor k_n)`.  Hence

```text
e_h(rho_tilde_n,c_tilde_n)
 =1-(1-e_n)^(k_n) >=1-exp(-1).                          (ONP4)
```

Pass to a tracial matrix ultraproduct.  Equation `(ONP3)` produces a genuine
representation of `Gamma`; its `Lambda` restriction has exact
odd-congruence lifts.  The class of `c_tilde_n` centralizes `Lambda`.
Therefore `odd-congruence-lambda-exact-sector-collapses` makes it centralize
all of `Gamma`, in particular the image of `h`.  Its target word is the
identity and has trace-square energy zero, contradicting `(ONP4)`.  This
proves `(ONG1)`.

The argument uses neither regular actor trace nor multiplicity control.
Tensor powers preserve exact factorization through the odd quotient, which
is why the qualitative exact-sector theorem upgrades to one uniform linear
constant on the entire sector.
