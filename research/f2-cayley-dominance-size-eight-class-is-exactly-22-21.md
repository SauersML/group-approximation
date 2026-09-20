---
rg: 2
id: f2-cayley-dominance-size-eight-class-is-exactly-22-21
kind: claim
title: The subgroup-dominance constant of a set is decided inside its span, which has dimension at most |S| - 1, so each size class is a finite computation; over all sets of size 8 in every F_2^k the supremum is exactly 22/21, and the radius-one balls B_s satisfy C(B_s) = (s(s-1) - j(j+1))/((s-1)(s-2)), equal to 22/21 at s = 8 and 16 and tending to 1
distinct_from:
  f2-cayley-subgroup-sets-are-constant-factor-optimal: that conjectures sup C(S) < infinity over all sizes; this settles the size class |S| = 8 exactly (every k, not only k <= 7 by search) and one infinite family with c -> infinity, and reduces every fixed size class to a finite check, but does not bound C(S) for |S| >= 16 in general.
  f2-cayley-sse-exact-census-small-k: that is a census of Cayley graphs at small k; this is a census of sets of a fixed size at every k, made finite by the span reduction.
  mass-only-spectral-relaxation-of-subgroup-dominance-is-order-c: that is a class kill for mass-profile proofs of the conjecture; this is about the sets themselves and gives evidence in the opposite direction (the true constants stay near 1 as c grows along the ball family).
artifacts:
  - research/f2-cayley-dominance-size-eight-class-proof.md
  - experiments/f2-dominance-census-2026-09-17/size_class_census.py
  - experiments/f2-dominance-census-2026-09-17/ball_family_check.py
  - experiments/f2-dominance-census-2026-09-17/census_s8.out
---

**ESTABLISHED.** Route: `f2-cayley-dominance-size-eight-class-proof`.

Notation is as in `f2-cayley-subgroup-sets-are-constant-factor-optimal`:
`|S| = s = 2^j`, `d_S(a) = |S \ (S+a)|/s`, and

```text
C(S) = min over distributions p on subgroups H of F_2^k with |H| = s  of  max_(a != 0) Pr_p[a not in H] / d_S(a).
```

## Statement

**Lemma 1 (span reduction).** Let `0 in S` and `V = span(S)`. Then `C(S)` computed
in `F_2^k` equals `C(S)` computed in `V`, and `dim V <= s - 1`. `C` is also invariant
under translation and under `GL(k, 2)`. So for each `s` the supremum of `C(S)` over
all `|S| = s` and all `k` is the maximum over the finitely many sets
`S = {0, e_1, ..., e_r} u T` with `log2 s <= r <= s - 1` and `T` a set of `s - 1 - r`
vectors of `F_2^r` of weight at least `2`.

**Theorem 2 (the size-8 class).** `sup { C(S) : |S| = 8, S in F_2^k, k >= 3 } = 22/21`.
The maximum is attained at the radius-one ball `{0, e_1, ..., e_7}` (r = 7) and at
`{0, e_1, ..., e_6, e_1 + ... + e_6}` (r = 6). Up to coordinate permutation there are
38 candidate sets. Every one has matching exact rational lower and upper certificates.
The next values are `296/285`, `32/31`, `52/51` and `64/63` (`census_s8.out`).

**Proposition 3 (radius-one balls).** For `s = 2^j >= 4` and `B_s = {0, e_1, ..., e_(s-1)}` in `F_2^(s-1)`,

```text
C(B_s) = (s(s-1) - j(j+1)) / ((s-1)(s-2)).
```

This gives `1, 22/21, 22/21, 481/465, 95/93` at `s = 4, 8, 16, 32, 64`, and
`C(B_s) = 1 + 2/s + O(j^2/s^2) -> 1`. The codimension here is
`c = s - 1 - j`, which tends to infinity.
The optimal primal law is the mixture `(j+1)/s` of uniform coordinate subspaces
`span{e_i : i in T}` (`|T| = j`) and `1 - (j+1)/s` of uniform even-weight subspaces
`{x : supp x <= T, |x| even}` (`|T| = j + 1`). The optimal dual law is uniform on the
vectors of weight 1 and 2.

## What it changes

* The prior data were a search at `k <= 7`, and the node recorded that the search
  cannot reach `k >= 8`. By Lemma 1, the size-8 class never needs `k > 7`. That class
  is now closed at every `k`: `22/21` is its exact value, not a search artefact.
* Any family with `C(S) -> infinity`, or any single set with `C(S) > 22/21`, must have
  `|S| >= 16`. The natural candidate with `c -> infinity` and many short approximate
  periods, the radius-one ball, has `C -> 1`.
* The maximum `22/21` is attained at both `s = 8` and `s = 16` by the ball family.
  Together with the column-generation data below, this suggests the sharper
  conjecture `C* = 22/21`. That is recorded as a conjecture, not established.

## Column-generation data at s = 16, 32 (not part of the ESTABLISHED statement)

`size_class_census.py search` does local search with exact pricing over all subgroups:
`200787` subgroups at `(k,s) = (8,16)`, `97155` at `(8,32)` and `3309747` at `(9,16)`.
The runs were partial and uncertified:

* `(8,16)`: maximum `1.0221`;
* `(8,32)`: maximum `1.0014`.

Both are below `22/21`. The logs are in `experiments/f2-dominance-census-2026-09-17/search_*.out`.

## Attempts

* **Span reduction plus exact certification (2026-09-20, swarm-0917-w23, finite-models).**
  This is the content above. Where it stops: the size class `s = 16` needs `r` up to
  `15`, and `F_2^15` has about `2^44` subgroups of dimension `4`. So the exact census
  stops at `s = 8`. For `s >= 16` only the ball family is proved exactly, and the rest
  is search.
