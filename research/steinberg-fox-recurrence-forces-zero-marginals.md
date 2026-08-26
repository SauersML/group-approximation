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

The latter possibility is now sharply fenced:
`steinberg-nonconstant-weights-generate-full-projective-module` shows that
translations together with the `u` Möbius pullback generate the complete
rank-one projective weight module.  Thus any nonconstant weighted packet,
together with the constant equations, recovers every pointwise slice rather
than a smaller closed frequency subsystem.  The pointwise system remains
live; the small-weighted-transform shortcut does not.

The first exceptional pointwise orbit is now understood exactly, and it
does not close the claim by itself.  The firewall
`steinberg-y-anchor-leaves-one-boundary-mode` shows that `Y` forces the
fiber `f(-1/4,0,t)` to one scalar `kappa` on `t!=0`, with
`P(-1/4,0)=-kappa`, while its `t=0` value is zero.  Both obvious remaining
`Y` equations are identities.  Applying `X` exports `kappa` into a coupled
`q`-difference and transverse `s`-difference cascade rather than killing
it locally.  Thus the live marginal problem is to control those transverse
branches using the full two-row pointwise system; further iteration of the
single exceptional projective orbit is insufficient.
