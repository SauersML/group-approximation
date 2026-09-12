---
rg: 2
id: steinberg-instability-from-leavitt-unit-hyperlinear
kind: route
title: A hyperlinear binary Leavitt unit group makes the Steinberg cover HS-unstable
target: leavitt-steinberg-hs-unstable
requires:
  - binary-leavitt-unit-group-hyperlinear
  - steinberg-hs-stability-equals-nonhyperlinearity
  - leavitt-gl-equals-el-and-perfect-unit-group
---

By `leavitt-gl-equals-el-and-perfect-unit-group` and the four-leaf prefix code
`M_4(L) ~= L`, the group `Q = EL_4(L_(F_2)(1,2)) = GL_4(L)` is isomorphic to
`L^x`. If `L^x` is hyperlinear, condition 3 of
`steinberg-hs-stability-equals-nonhyperlinearity` fails, and therefore so does
condition 1: `St_5(L)` is not normalized-HS stable.

Consequence for attackers. Every construction route into
`binary-leavitt-unit-group-hyperlinear` is also a route into this branch. These
include the 24k relative-unitary criterion, the singular near-state criterion,
and the projective relaxation `leavitt-unit-hyperlinear-iff-projective-hs-model`.
So is the stakes lemma `leavitt-hyperlinear-branch-implies-thompson-v-hyperlinear`:
selecting this branch proves that Thompson's `V` is hyperlinear.

**Cycle, on purpose.** See `leavitt-unit-hyperlinear-from-steinberg-instability`.
