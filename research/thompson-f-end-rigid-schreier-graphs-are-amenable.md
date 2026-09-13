---
rg: 2
id: thompson-f-end-rigid-schreier-graphs-are-amenable
kind: claim
title: Schreier graphs of Thompson's group F whose point stabilizers contain an end-rigid subgroup are amenable
distinct_from:
  thompson-f-is-amenable: that is amenability of F itself; this is amenability of the Schreier graphs of certain F-sets, which holds unconditionally and implies nothing about F.
  thompson-f-random-walks-are-not-liouville: that concerns bounded harmonic functions of random walks on F; this concerns Følner sets in Schreier graphs of F-sets.
artifacts:
  - research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13.md
---

**ESTABLISHED.** Let `S` be a finite symmetric generating set of Thompson's group `F`, let
`Y` be an `F`-set and `y ∈ Y`. For `c ∈ (0,1)` let `F_[c,1]` be the elements of `F` that are
the identity on `[0,c]`, and `F_[0,c]` those that are the identity on `[c,1]`. If
`Stab_F(y)` contains `F_[c,1]` or `F_[0,c]` for some `c`, then the Schreier graph of the orbit
`F·y` with respect to `S` is amenable. Either the orbit is finite, or for every `M` there is
a set of `M` orbit points with at most `sum_(s ∈ S) |k_s|` boundary pairs, where `2^(k_s)` is
the slope of `s` at `0`.

**Instances.**
- Every orbit of `F` on `(0,1)`, for every finite generating set.
- Every orbit of `F` on finite subsets of `(0,1)`.
- Every coset space `F/H` with `H ⊇ F_[c,1]` or `H ⊇ F_[0,c]`.

**Consequence.** No Ponzi scheme, doubling map or other non-amenability certificate for `F`
can be built on these Schreier graphs; see `thompson-f-has-a-nonamenable-orbital-schreier-graph`,
which this claim refutes. The mechanism: near `0` every element of `F` acts as a power of
`x_0`, so `r = x_0^(-(n-k_s)) s x_0^n` is the identity on `[0,c]` for large `n`, and long
`x_0`-rays toward the end are almost invariant.

**Scope.** Elementary and very likely folklore; no novelty is claimed. It decides nothing
about amenability of `F`.

Proof route: `thompson-f-end-rigid-schreier-graphs-are-amenable-proof`.
