---
rg: 2
id: local-or-simulation-loss-proof
kind: route
title: Charge each one-bit excitation to the backward support of a normalized term
target: local-or-simulation-has-linear-normalized-loss
requires: []
artifacts:
  - research/artifacts/local-or-simulation-loss-2026-09-12.md
---

For each physical term, its backward circuit support meets at most
`min{t,k b^D}` data inputs. A one-bit excitation outside that support has
exactly the vacuum expectation for the term, even with entangled fixed
ancillas. An excitation inside has expectation at most one. Averaging
over the `t` possible excitations and then over normalized term weights
gives at most `eta+min{1,k b^D/t}`. The asserted operator domination
bounds every such expectation below by `1/L-delta`, proving the result.

For sharpness without encoding, average all `k`-site OR projectors.
Its eigenvalue on a string of weight `r` is
`1-binomial(t-r,k)/binomial(t,k)`, with binomial coefficient zero when
`t-r<k`. This vanishes at `r=0`, has minimum `k/t` over `r>=1`, and
is at most one. Hence `P_t*k/t<=K<=P_t`. The artifact gives the full
proof and the precise quantum-PCP scope boundary.
