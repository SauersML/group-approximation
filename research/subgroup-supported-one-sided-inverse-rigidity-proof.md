---
rg: 2
id: subgroup-supported-one-sided-inverse-rigidity-proof
kind: route
title: Project onto the identity coset, then use direct finiteness of the corner
target: subgroup-supported-one-sided-inverse-rigidity
requires: []
artifacts:
  - research/artifacts/leavitt-rank-three-no-inverse-2026-08-18.md
---

## Direct proof

**Corners of a directly finite ring are directly finite.**  If `S` is directly
finite, `f = f^2 in S` and `a,b in fSf` satisfy `ab = f`, then
`a(1-f) = (1-f)b = 0`, so `(a+1-f)(b+1-f) = ab + (1-f) = 1`; direct finiteness
gives `(b+1-f)(a+1-f) = 1`, whose `fSf` component is `ba = f`.  So `f k[H] f`
is directly finite whenever `k[H]` is.

**Residually finite implies directly finite** (the hypothesis in the form
used downstream).  For every finite-index normal `N <= H`, `phi_N : k[H] ->
k[H/N]` is a ring map into a finite-dimensional algebra, which is directly
finite; so `ab = 1` gives `phi_N(ba - 1) = 0` for every `N`.  A nonzero
element of `k[H]` has finite support, and residual finiteness separates
finitely many group elements into distinct cosets of some `N`, so
`intersection_N ker(phi_N) = 0` and `ba = 1`.

**The projection.**  Decompose `k[G] = directsum_(Hg in H\G) k[Hg]` over right
`H`-cosets.  Left multiplication by an element of `k[H]` preserves each
summand, since `H·Hg = Hg`.  Suppose `alpha beta = f`.  Both `alpha` and `f`
lie in `k[H] = k[H·1]`, so comparing components in the summand `k[H]` gives

```text
alpha beta_H = f,
```

where `beta_H` is the component of `beta` supported on `H` — the rest of
`beta` contributes only to other cosets and is discarded.  Put
`b = f beta_H f in f k[H] f`.  Then `alpha b = (alpha f) beta_H f =
alpha beta_H f = f f = f`, using `alpha f = alpha`.  By the first paragraph
`f k[H] f` is directly finite, so `b alpha = f` as well.

For the hypothesis `beta alpha = f`, decompose over LEFT cosets `gH` instead;
right multiplication by `k[H]` preserves each summand and the same three lines
apply.

**The consequences.**  Item 1 is the case `f = 1`.  For item 2, apply the ring
map `rho` to `alpha b = b alpha = f`.

## Scope

No hypothesis on `G` beyond being a group, and none on `beta` at all.  The
proof uses nothing about `k` beyond its being a ring; the field hypothesis is
carried only because the residual-finiteness paragraph invokes
finite-dimensionality of `k[H/N]`.
