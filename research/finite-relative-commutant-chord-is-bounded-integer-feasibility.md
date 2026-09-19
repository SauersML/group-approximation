---
rg: 2
id: finite-relative-commutant-chord-is-bounded-integer-feasibility
kind: claim
title: Every finite relative-commutant chord reduces to one bounded integer system
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  chord-regauging-is-relative-commutant-feasibility: that characterizes closure by the existence of a common-commutant involution; this eliminates that involution and gives an explicit integer feasibility system for arbitrary, possibly noncommuting, separator algebras.
  commuting-separator-chord-is-capacitated-transport: that gives a bipartite max-flow criterion when the two separator algebras commute; this uses the full Wedderburn decomposition and applies without that hypothesis.
---

Use `(CRF1)--(CRF3)` and put

```text
M=A_0 vee A_1
 = direct-sum_lambda (M_(n_lambda)(C) tensor 1_(m_lambda)) (WIF1)
```

in standard finite-dimensional form.  For a minimal separator atom
`e_(i,s)`, write its component in the `lambda` block as

```text
e_(i,s,lambda) tensor 1_(m_lambda)
```

and set

```text
r_(i,s,lambda)=rank(e_(i,s,lambda)),
b_(i,s)=rank(e_(i,s)(1+X_i)/2).                         (WIF2)
```

The two endpoint regauges meet if and only if there are integers
`k_lambda` satisfying

```text
0 <= k_lambda <= m_lambda,
sum_lambda r_(i,s,lambda) k_lambda=b_(i,s)              (WIF3)
```

for `i=0,1` and every separator atom `s`.  Negative conditional ranks then
agree automatically.  Hence an arbitrary finite chord double-orbit is
decidable by a finite bounded integer search directly from the two separator
algebras and the two chord signs.

Equal unconditional ranks do not imply `(WIF3)`.  For the Pauli involutions
in `M_2(C)`, take `A_0=C^*(Z)`, `X_0=Z`, `A_1=C^*(X)`, and `X_1=X`.
Both chord signs have positive rank one, but `A_0 vee A_1=M_2(C)` has scalar
commutant.  Its sole Wedderburn multiplicity is `m_1=1`, so a
common-commutant involution has positive rank zero or two, never one.
