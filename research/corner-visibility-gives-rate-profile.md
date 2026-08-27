---
rg: 2
id: corner-visibility-gives-rate-profile
kind: route
title: Bounded trace gap makes the rate profile automatic
target: mf-trace-gap-defect-ratio-models
requires: [mf-invariant-corner-visibility]
---

## Why sufficient

`mf-invariant-corner-visibility`, in its corner-free form `(I')`, gives for
each finite `F` and each `delta>0` an operator-norm local model of `G` on `F`
with defect at most `delta` and `Re tr(phi(g)) <= 1-c_g`, the constant
depending only on `g`.  Diagonalize over an exhausting sequence of finite
sets with `delta_n = 1/n`: the resulting single sequence has
`epsilon_n <= 1/n -> 0` and trace gaps

```text
kappa_n = 1-Re tr(phi_n(g)) >= c_g > 0,
```

so `epsilon_n^2/kappa_n <= 1/(n^2 c_g) -> 0`, which is `(P1)`.  End proof.

## Consequence for the frontier

The two open holes of the `mf-implies-hyperlinear` cluster are therefore
*ordered*, not independent:

```text
mf-invariant-corner-visibility  =>  mf-trace-gap-defect-ratio-models
                                =>  mf-implies-hyperlinear.
```

The rate claim is the strictly weaker hypothesis --- it tolerates
`kappa_n -> 0` provided `epsilon_n^2` decays faster, whereas corner
visibility demands `kappa_n` bounded below --- so it is the better target of
the two, and `mf-implies-hyperlinear-via-invariant-corner` factors through
`mf-implies-hyperlinear-via-rank-profile`.  Keeping both routes is
deliberate: they record two different mechanisms for producing the trace
(structural corner versus amplification rate), and the weaker hypothesis is
the one to attack.

The ordering also transfers the sector-density verdict.  By
`sign-mark-rate-is-sector-density` the rate fails whenever property `(T)`
squeezes a sign mark onto a sector of density `O(epsilon_n^2)`; since corner
visibility implies the rate, it fails for those same model families --- as it
must, since a trace tending to `1` is exactly invisibility.
