---
rg: 2
id: iwahori-square-free-bs14-presentation
kind: claim
title: The Iwahori presentation needs no half-parabolic square-root coordinate
distinct_from:
  iwahori-square-root-presentation-is-bs14-plus-one-involution: that introduces the half-parabolic `S` in order to eliminate the second modular involution; this Tietze-eliminates `S` again while retaining the one-involution BS form.
  fourth-power-covariance-unfolds-square-root-branches: that proves a quantitative linear root-unfolding estimate between exact BS cores; this gives the exact square-free presentation underlying that estimate.
  far-sector-vertex-handled-edge-is-square-root: that frames the old reduction as selection of a square root of one parabolic; this shows that the full arithmetic edge remembers the root as a fixed word in the BS implementer and the squared parabolic.
---

The corrected Iwahori presentation is Tietze equivalent to

```text
PSL_2(Z[1/2])
 =<x,r,t | x^2=1, (xr)^2=1, (xt)^3=1,
             r t r^(-1)=t^4, (x t^2 r)^3=1>.          (SFP1)
```

Equivalently, using `x^2=1`, replace `(xr)^2=1` by
`x r x=r^(-1)`.  Here `t` is the full first-vertex parabolic.  The
subgroup `<r,t>` is again `BS(1,4)`.  No choice of a square root,
odd-order exponent, spectral branch, or additional generator is present.

The exact substitution from the old half-parabolic coordinate is

```text
t=s^2,                    s=r^(-1)t^2r.               (SFP2)
```

Therefore the four-relator relative extension problem over an exact BS core
can be written entirely as

```text
x^2=1,       x r x=r^(-1),
(x t)^3=1,   (x t^2 r)^3=1.                           (SFP3)
```

The Tietze move is quantitatively safe in normalized HS norm with fixed
word-length constants.  In the old-to-new direction, if

```text
delta=||r s r^(-1)-s^4||_2,       t=s^2,
```

then the new BS defect is at most `2 delta`, the first cubic is unchanged,
and the new second cubic differs from the old one by at most `3 delta`.
In the new-to-old direction, if

```text
delta=||r t r^(-1)-t^4||_2,       s=r^(-1)t^2r,
```

then `||s^2-t||_2<=delta`, the old BS defect is at most `2 delta`, the
first cubic gains at most `3 delta`, and the second cubic is unchanged.
Thus vanishing normalized-HS defects are equivalent in the two coordinate
systems with dimension-independent linear loss.

This removes the odd-root branch from the endpoint rather than trying to
round it.  The Hadamard obstruction in
`relative-first-triangle-rounding-has-an-odd-root-branch-firewall` applies
only to the old alternating algorithm which discarded `r` and then tried to
reconstruct `s` from `s^2`.  The actual square-free tuple retains `(r,t)`
throughout, and `fourth-power-covariance-unfolds-square-root-branches` shows
that returning to `s` later is a dimension-free Lipschitz coordinate change.

The remaining global theorem is correspondingly smaller: authenticate an
exact congruence endpoint for the exact BS core `(r,t)` and its one extending
involution `x`.  There is no independent half-root-selection subproblem.

