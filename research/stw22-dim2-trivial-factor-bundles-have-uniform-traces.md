---
rg: 2
id: stw22-dim2-trivial-factor-bundles-have-uniform-traces
kind: claim
title: Trivial bundles of arbitrary separable II1 factors over two-dimensional bases have only canonical traces
distinct_from:
  farah-vaccaro-one-dim-trivial-bundles-uniform-traces: that published theorem treats arbitrary II1 factors over bases of dimension at most one; the present theorem crosses the first unresolved topological dimension.
  stw22-finite-dimensional-trivial-field-traces: that theorem treats every finite-dimensional base but only the hyperfinite II1 factor; the present theorem permits every separable II1 factor and stops sharply at dimension two because only uniform loop filling is used.
  stw22-dim1-factor-bundles-have-uniform-traces: that theorem permits nontrivial countably generated bundles but only over one-dimensional bases; the present theorem is two-dimensional and uses a fixed arbitrary factor fibre.
artifacts:
  - research/artifacts/stw22-dim2-arbitrary-factor-breakthrough-2026-08-30.md
---

Let `(N,tau)` be any II1 factor with separable predual and let `X` be a
compact Hausdorff space with covering dimension at most two. For the trivial
W-star bundle

```text
C_sigma(X,N)
 ={a:X->N : a is bounded and 2-norm continuous},
```

every tracial state is uniquely of the form

```text
rho_mu(a)=integral_X tau(a(x)) dmu(x)                   (DT1)
```

for a Radon probability measure `mu` on `X`. Equivalently,

```text
T(C_sigma(X,N)) = Prob(X)
```

under the canonical affine identification, and every trace is continuous
for the uniform `2`-norm.

Thus STW Problem XXII has a positive answer for all trivial separable
factor bundles through covering dimension two, including
`C_sigma(S^2,L(F_2))` and trivial bundles with property-Gamma-free,
non-McDuff fibres. No nuclearity, hyperfiniteness, property Gamma, or local
matrix approximation is assumed.
