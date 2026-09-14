---
rg: 2
id: monomial-rank-models-are-hamming-models
kind: claim
title: Over a finite field, rank distance between monomial matrices is Hamming distance up to a factor two, so monomial linear sofic approximations are sofic approximations
distinct_from:
  signed-monomial-tracial-images-are-sofic: that compares signed permutation coordinates with Hamming distance in the normalized Hilbert--Schmidt norm; this is the normalized-rank comparison for monomial matrices whose labels lie in the multiplicative group of a finite field.
  uniformly-discrete-block-monomial-images-are-sofic: that treats block-monomial Hilbert--Schmidt models with finite block groups under a uniform character gap; this treats scalar monomial labels in the rank metric, where no gap hypothesis is needed.
  block-unipotent-rank-models-of-leavitt-el3-are-trivial: that excludes the module-type family of rank models through direct finiteness of corners; this excludes the permutation-type family through soficity.
artifacts:
  - research/artifacts/leavitt-unit-rank-model-construction-audit-2026-09-12.md
---

**ESTABLISHED.** Let `F` be a finite field and `Mon_N(F) <= GL_N(F)` the monomial
matrices. They act faithfully on `X_N = F^x x {1, ..., N}` by
`j(A)(lambda, i) = (c lambda, pi(i))`, where `A e_i = c e_(pi(i))`. For all
`A, B in Mon_N(F)`,

```text
(1/2) d_H(j(A), j(B))   <=   rk(A - B) / N   <=   d_H(j(A), j(B)),
```

with `d_H` the normalized Hamming distance on `X_N`.

Consequently, let `sigma_k : G -> GL_(N_k)(F)` be asymptotically multiplicative in
normalized rank, separate elements (for each `g != 1`, `rk(sigma_k(g) - 1) / N_k` is
bounded away from `0`), and take values within `o(N_k)` rank of `Mon_(N_k)(F)`. Then
`j` applied to the nearby monomial matrices is a sofic approximation of `G`:
multiplicative defects at most double, and separation does not shrink.

**Consequence.** A nonsofic group has no monomial linear sofic approximation over any
finite field. Over `F_2` the monomial matrices are the permutation matrices, so linear
sofic approximations by permutation matrices are sofic approximations. This excludes the
permutation-type constructions from both gates:
- `binary-leavitt-unit-group-is-f2-linear-sofic`, since `R^x` is nonsofic
  (`openai-leavitt-unit-nonsofic`);
- `projective-ternary-group-is-f3-linear-sofic`, since `PG` is nonsofic
  (`projective-leavitt-unit-groups-mod-scalars-are-nonsofic`), and so is
  `L_(F_3)(1,2)^x` (`d-ary-leavitt-groups-nonsofic-over-finite-fields`).

## Attempts

Established; see `monomial-rank-models-are-hamming-models-proof`.
