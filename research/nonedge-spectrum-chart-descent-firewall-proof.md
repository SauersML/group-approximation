---
rg: 2
id: nonedge-spectrum-chart-descent-firewall-proof
kind: route
title: Move one endpoint inside the chart stabilizer and intersect cyclic Fourier supports
target: nonedge-spectrum-cannot-descend-to-forty-two-chart
requires:
  - native-sl3-group-is-hecke-graph-wreath-product
  - native-forty-two-shell-has-a-noncommuting-pair
  - no-native-arithmetic-relator-breaks-the-bernoulli-quotient
---

Conjugating the elementary matrix `d=x_21(1)` by the two diagonal directions
gives `(KSD3)`. Hence `d` belongs to the stabilizer `D` of `hC` and moves
`h^(-1)C`. Since the Hecke graph is actor invariant, both resulting pairs
are nonedges.

In a graph product, the support of a cyclically reduced word is unchanged by
taking a nonzero power. The two powers in `(KSD4)` have different supports,
so the cyclic subgroups intersect trivially.

For subgroups `H_1,H_2<G`, canonical Fourier expansion gives

```text
L(H_1) cap L(H_2)=L(H_1 cap H_2).                       (NSD1)
```

More quantitatively, if `T_i in L(H_i)` and `H_1 cap H_2={1}`, their
centered Fourier supports are disjoint, so

```text
tau(T_1 T_2)=tau(T_1)tau(T_2).                          (NSD2)
```

Apply `(NSD2)` to `E` and `dEd^(-1)` to obtain `(KSD6)` and then expand the
squared norm to get `(KSD7)`.

For `(KSD10)`, the canonical moments make `rho_n(kappa)` converge in moments
to a Haar unitary because every nonzero power of `kappa` is a nonidentity
group word. Approximate the boundary-null indicator of `Delta` in `L2` by
Laurent polynomials. Canonical mixed moments of `kappa` and
`d kappa d^(-1)`, together with `(KSD4)`, converge to `(NSD2)`. The `L2`
approximation then transfers `(KSD6)--(KSD7)` to the exact spectral
projections `E_n`.
