---
rg: 2
id: gkp-sofic-action-is-liftable-hamming-chart-family
kind: claim
title: A discrete action is sofic exactly when it embeds equivariantly into the universal liftable Hamming-chart action
distinct_from:
  gkp-free-wreath-permanence: that uses a sofic action to prove a free generalized wreath product sofic; this records the exact ultraproduct data which constitute soficity of the underlying action.
  sl3-prime-coset-action-exact-atlas-firewall: that excludes correction to exact finite arithmetic actions for one specific co-dense pair; this is the general positive-density chart characterization.
---

**ESTABLISHED LITERATURE INPUT.**  Gao--Kunnawalkam Elayavalli--Patchell,
*Soficity for group actions on sets and applications*, Research in the
Mathematical Sciences 12 (2025), 48, Definition 2.1 and Proposition 2.9.

For an action `G curvearrowright X`, soficity is equivalent to the existence
of

```text
sigma:G -> product_omega Sym(Omega_n)
```

and, for every `x in X`, liftable label maps

```text
ell_x=[ell_(x,n)],   ell_(x,n):Omega_n->N,              (LHC1)
```

such that

```text
ell_(gx)=ell_x composed_with sigma(g)^(-1) a.e.,
mu{ell_x != ell_y}=1                    (x!=y).          (LHC2)
```

Equivalently, on every finite action window, a proportion tending to one of
the carrier sites `s in Omega_n` supports an injective chart

```text
x |-> ell_(x,n)(s)
```

and these charts are transported coherently by the same approximate
permutations `sigma_n(g)`.

Thus the minimal extra payload beyond a root coefficient is a
**positive-density common-carrier family** of multiplicative equality
coordinates, not another scalar inner product at the root.

PRIMARY SOURCE
https://doi.org/10.1007/s40687-025-00526-6
