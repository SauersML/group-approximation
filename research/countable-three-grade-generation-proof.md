---
rg: 2
id: countable-three-grade-generation-proof
kind: route
title: Properly color each cyclic orbit graph and sum the recovered partial arrows
target: countable-three-grade-cells-generate-the-whole-crossed-product
requires:
  - three-actor-grades-support-an-exact-hadamard-cell
---

Fix `t in T`. Choose a countable Boolean algebra `(B_j)_j` generating the
measurable sets modulo null sets and closed under complements. Since `t` is
essentially free, for almost every `x` there is a `j` with

```text
x in B_j,       t^(-1)x notin B_j.
```

Put

```text
E_j=B_j minus alpha_t(B_j).
```

The sets `E_j` cover `K` modulo null sets. Moreover

```text
E_j intersect alpha_t(E_j)=empty:                     (CTP1)
```

if `x` belonged to both, then `x in E_j subset B_j`, while
`x in alpha_t(E_j) subset alpha_t(B_j)`, contradicting the definition of
`E_j`. Disjointize the cover in its enumeration order:

```text
q_(t,1)=E_1,
q_(t,n)=E_n minus union_(j<n)E_j.
```

Each `q_(t,n)` remains disjoint from its `t`-translate, and the nonzero
members form a countable partition of `1`. Applying `alpha_(t^(-1))` to
that disjointness gives `(CTG2)`.

For each nonzero member define `(CTG3)`. The proof of
`three-actor-grades-support-an-exact-hadamard-cell` applies verbatim. Because
`v_(t,n)` has initial projection `p_(t,n)` and final projection `q_(t,n)`, a
direct compression of `(CTG3)` gives `(CTG4)`. Finally

```text
sum_n v_(t,n) = (sum_n q_(t,n))U_t=U_t
```

in the strong operator topology. A von Neumann algebra is strongly closed,
so it contains `U_t`. This proves the reverse inclusion in `(CTG1)`; the
forward inclusion is immediate from `(CTG3)`.

If `<T>` is amenable, `D rtimes <T>` is an amenable finite von Neumann
algebra. Its tracial von Neumann subalgebras are expected and amenable, hence
Connes embeddable. The virtually-free conclusion follows separately from
`abelian-by-virtually-free-groups-are-sofic` and Pontryagin duality.

