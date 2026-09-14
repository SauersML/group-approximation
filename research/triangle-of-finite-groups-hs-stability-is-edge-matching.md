---
rg: 2
id: triangle-of-finite-groups-hs-stability-is-edge-matching
kind: claim
title: Flexible HS stability of a triangle of finite groups is the gluing of almost-matching genuine vertex representations
distinct_from:
  gowers-hatami-finite-group-hs-stability: that is stability of a single finite group with universal constants; this uses it on each vertex group and isolates what stability of the colimit asks beyond the vertex groups, namely gluing along the edge groups
  flexible-hs-stability-descends-to-retracts-finite-index: that transports flexible stability from a Kazhdan group to finite-index subgroups; this restates flexible stability of a colimit of finite groups as a property of tuples of genuine representations of the vertex groups
  kazhdan-hs-instability-lives-on-properly-nonamenable-limits: that reduces HS stability of a Kazhdan group to properly non-amenable asymptotic representations; this is a presentation-level reduction for colimits of finite groups, with no property (T) and no ultraproduct
---

**ESTABLISHED.**

**Setting.**
- `X_0, X_1, X_2` are finite groups.
- For each edge `e = {i,j}` there is a finite group `A_e` with injections `ι_{e,i} : A_e → X_i` and
  `ι_{e,j} : A_e → X_j`.
- `G` is the colimit: the quotient of `X_0 ∗ X_1 ∗ X_2` by `ι_{e,i}(x) = ι_{e,j}(x)` for every edge
  `e` and every `x ∈ A_e`.
- Write `x` also for the image of `x ∈ X_i` in `G`. The vertex groups need not inject into `G`.

**Definitions.**
- *Flexible HS stability* is Dogon's Definition 1.2 (arXiv:2211.10492v3). For every asymptotic
  representation `σ_n : G → U(d_n)` (pointwise, normalized HS) there are genuine
  `π_n : G → U(D_n)`, `D_n ≥ d_n`, `D_n/d_n → 1`, with `||σ_n(g) − P_n π_n(g) P_n*||_2 → 0` for all
  `g`. Here `P_n` is the co-isometry onto the first `d_n` coordinates.
- *(EM), edge matching.* For all `d_n` and genuine representations `ρ_{i,n} : X_i → U(d_n)` with

  ```text
  ||ρ_{i,n}(ι_{e,i}(x)) − ρ_{j,n}(ι_{e,j}(x))||_2 → 0      for every edge e = {i,j} and x ∈ A_e,
  ```

  there are genuine `π_n : G → U(D_n)`, `D_n/d_n → 1`, with `||ρ_{i,n}(x) − P_n π_n(x) P_n*||_2 → 0`
  for every `i` and `x ∈ X_i`.

**Theorem.** `G` is flexibly HS stable if and only if (EM) holds.

**What it isolates.** Each vertex group is finite, hence strictly HS stable. Stability of `G` is
then only about gluing: three genuine representations of the vertex groups on a common space,
almost agreeing on the edge groups, must be close to the restrictions of one genuine representation
of `G` after `o(d_n)` padding. For `G_{HB_2}(7)` this is the equivalent form recorded in
`ghb7-flexibly-hs-stable`.

**Credit.** Elementary. No priority is claimed.

DERIVATION
triangle-of-finite-groups-hs-stability-edge-matching-proof
