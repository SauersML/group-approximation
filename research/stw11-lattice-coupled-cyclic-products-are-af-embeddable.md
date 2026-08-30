---
rg: 2
id: stw11-lattice-coupled-cyclic-products-are-af-embeddable
kind: claim
title: Stable finiteness is equivalent to AF-embeddability for lattice-coupled products of cyclic systems
distinct_from:
  stw99-problem-xi-zd-crossed-stably-finite-qd: that asks about arbitrary Z^d-actions; this proves the full implication, including AF-embeddability, for actions obtained by coupling finitely many arbitrary cyclic systems through an integer lattice map.
  stw11-clopen-exhaustion-glues-qd: that glues quasidiagonality across a compact-open support extension and gives no AF embedding; this has no support-filtration hypothesis and produces an AF embedding from the product-of-cyclic geometry.
  stw11-transfinite-cumulative-clopen-filtrations-glue-qd: that treats transfinite cumulative compact-open filtrations; this instead treats skew and diagonal higher-rank couplings and concludes AF-embeddability.
artifacts:
  - research/artifacts/stw11-lattice-coupled-cyclic-products-audit-2026-08-30.md
---

Let `d,m>=1`, let `X_i` be nonempty compact metrisable spaces, and let
`alpha_i` be a homeomorphism of `X_i`.  Fix a homomorphism

```text
L:Z^d -> Z^m.
```

On `X=product_(i=1)^m X_i`, let `Z^d` act by

```text
g.(x_1,...,x_m)
  =(alpha_1^(L(g)_1)(x_1),...,alpha_m^(L(g)_m)(x_m)).       (LC1)
```

Write `H=L(Z^d)` and call `i` active when the `i`-th coordinate projection
of `H` is nonzero.  The following conditions are equivalent:

1. `C(X) rtimes Z^d` is stably finite;
2. for every active `i`, `C(X_i) rtimes_(alpha_i) Z` is stably finite;
3. no active `alpha_i` admits an open set `U subset X_i` with
   `alpha_i(U)` a proper subset of `U`;
4. `C(X) rtimes Z^d` is AF-embeddable;
5. `C(X) rtimes Z^d` is quasidiagonal.

Thus Problem XI has a positive answer for every lattice-coupled finite product
of cyclic systems.  The lattice map need not be injective, surjective, diagonal,
or have finite-index image.  In particular, the theorem includes genuinely
higher-rank skew actions for which every generator moves several factors.

For example, for arbitrary homeomorphisms `alpha_1,alpha_2` and

```text
L(n_1,n_2)=(n_1+2n_2,3n_1+n_2),
```

stable finiteness of the resulting `Z^2`-crossed product on `X_1 times X_2`
already forces it to embed into an AF algebra.  No faithful invariant measure,
tracelessness, zero-dimensionality, or compact-open support filtration is
assumed.
