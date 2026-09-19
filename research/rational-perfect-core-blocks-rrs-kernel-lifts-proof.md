---
rg: 2
id: rational-perfect-core-blocks-rrs-kernel-lifts-proof
kind: route
title: Push rational perfectness into every term of the kernel's rational derived series
target: rational-perfect-core-blocks-rrs-kernel-lifts
requires: []
artifacts:
  - research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md
---

Put `K=ker(q)` and `L=Phi(R)`.  Since `q Phi(R)=pi(R)=1`, we have `L<=K`.
A homomorphic image of a rationally perfect group is rationally perfect:
if `y=Phi(x)` and some positive power of `x` lies in `[R,R]`, the same power
of `y` lies in `[L,L]`.  Thus `L=L_Q^(1)`, and inductively
`L=L_Q^(j)` for every `j`.

The rational derived series is functorial.  Applying the inclusion `L->K`
gives

    L = L_Q^(j) <= K_Q^(j)

for every `j`.  Residual rational solvability of `K` says that the intersection
of the groups on the right is trivial.  Hence `L=1`, i.e. `Phi(R)=1`.

If `R` is perfect then so is `L`.  Repeating the identical argument with the
ordinary derived series proves the residually solvable version.
