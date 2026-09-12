---
rg: 2
id: leavitt-hs-stable-from-channel-rounding
kind: route
title: Select the stable Steinberg branch from dimension-free channel rounding
target: leavitt-steinberg-hs-stable
requires: [bistochastic-near-idempotents-round-dimension-free, leavitt-channel-rounding-forces-nonhyperlinearity, steinberg-hs-stability-equals-nonhyperlinearity]
---

The rounding premise and the conditional theorem make
`Q=L_(F_2)(1,2)^x=EL_4(L_(F_2)(1,2))` nonhyperlinear. By condition 3 of
`steinberg-hs-stability-equals-nonhyperlinearity`, nonhyperlinearity of `Q`
is equivalent to normalized-HS stability of `St_5(L_(F_2)(1,2))`, which is
the target.

On this branch the whole remaining difficulty is the matrix statement in the
first prerequisite. The contrapositive is the route
`channel-rounding-fails-on-the-unstable-branch`.
