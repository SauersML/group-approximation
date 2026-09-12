---
rg: 2
id: sublinear-block-poisons-normalized-torsion
kind: claim
title: Arbitrary sublinear corners poison normalized log determinant and torsion without changing a microstate
distinct_from:
  additive-index-instability: that observes tensor amplification of an additive index; this is an orthogonal firewall under adjoining arbitrary `o(d)`-dimensional direct-sum corners.
  index-density-is-amplification-stable: index density survives tensor amplification; unbounded spectral statistics still fail because a vanishing-rank corner can carry exponentially small singular values.
---

Let `V_n` be a `d_n`-dimensional microstate tuple and let `W_n` be any
`r_n`-dimensional unitary tuple with `r_n/d_n->0`. Then

```text
Z_n=V_n direct_sum W_n
```

is a microstate for the same trace. For every fixed word `w` and relator
polynomial `R`,

```text
|tr(w(Z_n))-tr(w(V_n))| <= 2r_n/(d_n+r_n),
||R(Z_n)||_2^2
 = d_n/(d_n+r_n)||R(V_n)||_2^2
 + r_n/(d_n+r_n)||R(W_n)||_2^2.
```

For a square polynomial evaluation with invertible blocks, normalized log
determinant is the same dimension-weighted direct sum. An `o(d_n)` block with
superexponentially small singular values can therefore change it by order one
or send it to `-infinity`. Alternating log-determinant expressions defining
normalized torsion obey the same formula.

Hence every viable microstate statistic needs an **`o(d)`-corner contamination
firewall**. Bounded continuous spectral statistics have it; `log` at zero does
not. A determinant identity derived only from multiplicativity, elementary
stabilization, `AB/BA`, or cancellation of contractible summands cannot help,
because the same identity holds for Fuglede--Kadison determinant in every
finite von Neumann algebra.
