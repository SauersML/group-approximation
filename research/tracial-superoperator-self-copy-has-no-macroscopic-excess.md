---
rg: 2
id: tracial-superoperator-self-copy-has-no-macroscopic-excess
kind: claim
title: A one-sided self-copy has no positive-density excess fixed sector in the adjoint tracial ultraproduct
distinct_from:
  property-t-hs-positive-density-commutant-no-growth: That gives a fixed-cutoff quantitative finite-stage O(delta) estimate using property (T); this is an exact ultraproduct projection identity with no property (T), no spectral gap, and no fixed cutoff.
  matricial-mautner-fixed-subspace: That identifies Kazhdan projections in an operator-norm matrix corona; this works in a normalized-HS tracial ultraproduct of adjoint superoperators and only controls macroscopic operator-space sectors.
  commutant-no-growth: That compares exact finite-dimensional commutants by integer dimension; this compares asymptotic fixed-vector projections after passing to the tracial ultraproduct.
artifacts:
  - notes/NONHYPERLINEAR_FINITE_MEMORY_REYNOLDS_AUDIT.md
---

Let `L=<Q>` be finitely generated, let `tLt^(-1)=H<=L`, and let
`u_n:G->U(d_n)` be any normalized-HS asymptotic representation.  On the
`d_n^2`-dimensional operator space put

```text
S_n(g)=u_n(g) tensor conjugate(u_n(g)).
```

In the tracial matrix ultraproduct, `S(g)=[S_n(g)]` is an exact unitary
representation.  Define

```text
Delta_L=sum_(q in Q)(S(q)-1)^*(S(q)-1),
p_L=1_{0}(Delta_L),
```

and define `p_H` using `tQt^(-1)`.  Then

```text
p_L=p_H.                                               (TSS1)
```

Consequently, if projections `E_n` have adjoint normalized trace bounded
below and satisfy

```text
||(S_n(h)-1)E_n||_2 -> 0       for h in tQt^(-1),
```

then the same convergence holds for every `q in Q`.

The conclusion is deliberately macroscopic.  A child-only asymptotic
commutant carried by `o(d_n^2)` operator directions disappears in this
tracial ultraproduct and is not excluded.

