---
rg: 2
id: leavitt-full-radical-via-dimension-descent
kind: route
title: Feed a dimension-reducing repair operation to the minimality contradiction
target: property-t-free-leavitt-full-mf-radical
requires:
  - dimension-descent-criterion-for-non-mf
  - binary-leavitt-dimension-descent-operation
artifacts:
  - research/artifacts/dimension-descent-criterion-2026-09-07.md
---

## Why sufficient

The second prerequisite supplies `epsilon_0` and the operation for the binary
Leavitt unit group `H`, with `z` a nontrivial involution.  The first turns
that into `z in Res_MF(H)`.

`H` is simple, so the normal closure of `z` is `H`, and the MF residual is
normal, so `Res_MF(H) = H`.

Nothing in either prerequisite uses property (T), a Kazhdan projection, or a
compression configuration, so this route reaches the goal from a purely
matricial construction.
