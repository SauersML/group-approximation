---
rg: 2
id: stw99-lxvi-build-car-from-dyadic-v-chain
kind: route
title: Realize each monoid halving as a nested projection decomposition
target: stw99-lxvi-car-corner-iff-coherent-dyadic-v-chain
requires: []
---

Suppose first that CAR embeds unitally in `pBp`.  At its standard `n`th
matrix stage, let `e_n` be a minimal projection, with `e_0=p`.  The standard
inclusion doubles each minimal projection, so

```text
[e_n]=2[e_(n+1)]
```

in `V(B)`.  Taking `x_n=[e_n]` gives the chain.

Conversely, suppose the chain `(x_n)` is given.  We first record how to
realize one equality inside a corner.  If `q in B` is a projection with
`[q]=2x_(n+1)`, choose a matrix projection `e` representing `x_(n+1)`.
The equality in `V(B)` gives a partial isometry in `M_infinity(B)` carrying
`e directSum e` onto `q`.  Transporting the two diagonal summands produces
orthogonal equivalent projections

```text
q^(0),q^(1) <= q,        q^(0)+q^(1)=q,
[q^(i)]=x_(n+1).
```

Because they lie below the copy of `q in B`, these transported projections
belong to `qBq`, not merely to a matrix amplification.

Starting with `q=p`, perform this construction recursively.  At level `n`,
the corner is decomposed into `2^n` mutually equivalent projections of class
`x_n`.  Split one representative using `x_n=2x_(n+1)` and transport that
split across matrix units to every other level-`n` summand.  The resulting
`2^(n+1)` equivalent projections refine the preceding decomposition.

A decomposition of `p` into `2^n` equivalent projections supplies unital
matrix units for `M_(2^n)` in `pBp`.  The transported refinements can be
chosen so that the resulting embeddings satisfy

```text
M_(2^n) -> M_(2^(n+1)),       a |-> a tensor 1_2.
```

Their inductive limit is the required unital CAR embedding.
