---
rg: 2
id: averaged-subalgebra-energy-repairs-bistochastic-channels
kind: claim
title: Averaged subalgebra energy controls exact bistochastic bimodule repair independently of dimension
distinct_from:
  near-fixed-masas-round-channels-but-exclude-native-heat: That repairs an approximately fixed maximal abelian algebra to Schur form; this allows arbitrary represented matrix algebras and their multiplicities.
artifacts:
  - research/artifacts/subalgebra-energy-and-bistochastic-kraus-repair-2026-09-08.md
---

Let `P:M_d->M_d` be self-adjoint on normalized `L^2`, unital,
trace-preserving and completely positive. For a unital subalgebra
`B subset M_d`, put

```text
a_B(P)=integral_(u in U(B)) [1-Re tr(u*P(u))] du.
```

There is a self-adjoint bistochastic completely positive map `Q`
that fixes `B` pointwise and is exactly `B`-bimodular, with

```text
||P-Q||_(infinity->2) <= 2 sqrt(2a_B(P)).
```

There is no bound on the dimension or representation multiplicities
of `B`. Conversely every map fixing `B` pointwise has distance from
`P` at least `a_B(P)` in this norm. A two-dimensional example shows
that the square-root dependence cannot generally be improved to a
linear dependence on `a_B(P)`.

This repairs the action on an already supplied algebra. It does not
extract a suitable algebra from near idempotence. If in addition
`beta=||(I-E_B)P||_(infinity->2)`, the same construction gives

```text
||P-E_B||_(infinity->2) <= beta+4 sqrt(2a_B(P)).
```

The full heat-rounding problem and nonhyperlinearity remain open.

DERIVATION
central-kraus-transport-repairs-subalgebra-bimodularity
