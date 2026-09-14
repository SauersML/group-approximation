---
rg: 2
id: channel-rounding-fails-on-the-unstable-branch
kind: route
title: An unstable Steinberg cover makes the native heat maps a rounding counterexample
target: bistochastic-channel-rounding-fails
requires: [leavitt-steinberg-hs-unstable, steinberg-hs-stability-equals-nonhyperlinearity, leavitt-channel-rounding-forces-nonhyperlinearity]
---

If `St_5(L_(F_2)(1,2))` is normalized-HS unstable, condition 3 of
`steinberg-hs-stability-equals-nonhyperlinearity` makes `L_(F_2)(1,2)^x`
hyperlinear. The contrapositive of
`leavitt-channel-rounding-forces-nonhyperlinearity` then says no
dimension-free rounding function exists.

Put `f(delta)=sup` of the distance to algebra expectations over all maps of
defect at most `delta`. Rounding is exactly `f(delta)->0`. Its failure gives
`c>0` and maps `P_n` with defects tending to zero at distance at least `c`,
which is the target. Concretely, the failing maps are native heat maps of
canonical microstates of `L_(F_2)(1,2)^x`, at admissible times, for the
global group or for the native corner subgroup.
