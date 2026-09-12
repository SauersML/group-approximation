---
rg: 2
id: stw27-real-rank-zero-block-division-proof
kind: route
title: Divide projection corners by large matrix blocks and exhaust hereditary subalgebras
target: stw27-real-rank-zero-almost-divisibility
requires:
  - perera-rordam-large-matrix-blocks-real-rank-zero
artifacts:
  - research/artifacts/stw27-real-rank-zero-divisibility-audit-2026-08-30.md
---

Write `S=Cu(A)`.  Real rank zero passes to `A tensor K`, to hereditary
subalgebras, and to projection corners.

## Compact division inside a projection corner

Let `p` be a nonzero projection in `A tensor K` and fix `n>=2`.  The unital
corner

```text
B=p(A tensor K)p
```

is simple and Morita equivalent to `A`.  It cannot have a nonzero
finite-dimensional representation: such a representation is faithful by
simplicity, so `B` would be finite dimensional; Morita equivalence would
then make `A` elementary, contrary to the non-type-I hypothesis.

Apply the Perera--Rordam large-block theorem to `B` with
`N=n(n-1)`.  It gives a unital star-homomorphism

```text
phi: direct-sum_i M_{r_i} --> B,             r_i>=n(n-1).
```

Let `e_i` be a rank-one projection in the `i`th matrix summand and put

```text
k_i=floor(r_i/n),             y=sum_i k_i[phi(e_i)] in S.
```

Because the homomorphism is unital,

```text
[p]=sum_i r_i[phi(e_i)].
```

Write `r_i=n k_i+s_i`, where `0<=s_i<=n-1`.  The lower bound on `r_i`
gives `k_i>=n-1`, and hence `s_i<=k_i`.  Therefore

```text
n k_i <= r_i <= (n+1)k_i
```

for every `i`.  Adding in `S` proves

```text
n y <= [p] <= (n+1)y.                                      (1)
```

For `n=1`, take `y=[p]`; then the analogous inequalities are immediate.

## From compact classes to arbitrary way-below pairs

Fix `x'<<x` in `S`.  Represent `x=[a]` for
`a in (A tensor K)_+`.  Since the hereditary algebra `Her(a)` has real rank
zero and is sigma-unital, it has an increasing approximate unit of
projections `(p_j)`.  In `Cu(A)`,

```text
[p_1] <= [p_2] <= ... ,             sup_j [p_j]=[a]=x.
```

The defining property of `x'<<x` gives an index `j` with
`x'<=[p_j]`.  If `p_j=0`, then `x'=0` and `y=0` works.  Otherwise apply
`(1)` in the corner of `p_j`.  The resulting `y` satisfies

```text
n y <= [p_j] <= x,
x' <= [p_j] <= (n+1)y.
```

These are precisely the two inequalities in the definition of almost
divisibility.

Strict comparison is the almost-unperforation axiom for `Cu(A)` in the
simple stably finite setting, while purity is almost unperforation together
with almost divisibility.  The final assertion follows.  If the algebra is
not stably finite, the displayed almost-divisibility conclusion remains
valid; the strict-comparison corollary is read in the usual STW setting.
