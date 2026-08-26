---
rg: 2
id: steinberg-fox-recurrence-forces-zero-marginals
kind: claim
title: The Steinberg chord Fox recurrence forces both two-dimensional marginals to vanish
---

Every solution of `(SCA4)`, with exceptional values evaluated by
`steinberg-tree-cuts-are-five-marginals`, satisfies

```text
P(a,b)=0,                    H(c,d)=0                 (SZM1)
```

for all arguments.  Hence `A=C=T=0` as well.

## Attempts

Summing a recurrence over one coordinate does not directly close: the maps
`tau_A,tau_B,tau_u` mix the fibers.  The boundary-slice equations give
explicit differences of `P` or `H`, but a proof must still force their
absolute values rather than only those differences.

`steinberg-fox-marginal-pushes-are-explicit` eliminates the remaining
abstract `u`-push by a complete point/plane case split.  However,
`steinberg-pushed-marginal-sums-have-no-new-closure` shows that unweighted
fiber and fractional-linear-orbit sums only recover the existing `A,C,T`
balance identities.  Any closure must use the full pointwise system or a
genuinely weighted transform.
