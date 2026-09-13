---
rg: 2
id: weyl-algebra-is-exactly-matricial
kind: claim
title: The rational Weyl algebra has no finite-dimensional representations but embeds unitally in an ultraproduct of the matrix algebras M_p(F_p)
artifacts:
  - research/artifacts/un-converse-stable-finiteness-boundary-2026-09-13.md
---

**ESTABLISHED** (route `weyl-algebra-is-exactly-matricial-proof`; artifact §5). Unreviewed; classical folklore
(reduction mod p).

Let `A_1(Q) = Q<x,y>/(yx − xy − 1)` and let `ω` be a nonprincipal ultrafilter on the primes. There is an
injective unital ring homomorphism `A_1(Q) → ∏_ω M_p(F_p)`. So `A_1(Q)` is a simple domain with no nonzero
finite-dimensional module that is nevertheless exactly matricial, and every `GL_N(A_1(Q))` is LEF
(`exactly-matricial-rings-have-lef-general-linear-groups`).

Role: a calibration for `stably-mf-elementary-groups-force-matricial-rings`. Matricial models can live only in
characteristic `p` while the ring has characteristic 0.
