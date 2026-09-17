---
rg: 2
id: sdp-fixed-precision-solvable-gls
kind: claim
title: A semidefinite program with a known inner and outer ball in its affine hull is solvable to additive precision eps in time polynomial in the data and log(R/r), log(1/eps) (Grotschel--Lovasz--Schrijver, as stated by de Klerk--Vallentin Theorem 1.1)
distinct_from:
  unique-games-entangled-value-approximable-by-sdp: that is Kempe--Regev--Toner's rounding for the entangled value of unique games; this is only the general Turing-model solvability of SDPs to fixed precision.
  low-label-threshold-rank-reductions-cannot-prove-ugc: that avoids numerical optimisation entirely by exact rational linear algebra; this is the solver import used by SDP-based obstructions.
---

**ESTABLISHED, BY CITATION.** Consider

```text
val = inf <C, X>   over X in S^n, X PSD, <A_j, X> = b_j (j = 1..m),
```

with rational data, and let `F` be its feasible set. Suppose a rational `X0` in
`F` and rational `r, R > 0` are known such that every `X` in the affine space
`X0 + L`, `L = {X : <A_j, X> = 0 for all j}`, with `||X - X0||_F <= r` lies in
`F`, and every `X` in `F` has `||X - X0||_F <= R`. Then for every rational
`eps > 0` one can find in polynomial time a rational `X*` in `F` with
`<C, X*> - val <= eps`. The polynomial is in `n`, `m`, `log2(R/r)`,
`log2(1/eps)` and the bit size of `X0, C, A_j, b_j`.

Credit: Grotschel, Lovasz, Schrijver, *Geometric Algorithms and Combinatorial
Optimization* (Springer 1988), via the ellipsoid method. The statement is
imported in the form of Theorem 1.1 of de Klerk--Vallentin, arXiv:1507.03549,
who reprove it with interior point methods. The verbatim text and the reading
of its ball notation are in the route.

DERIVATION sdp-fixed-precision-solvable-gls-citation
