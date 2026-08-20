---
rg: 2
id: packet-kazhdan-commutant-placement-decouples-proof
kind: route
title: Put the compressor and a forbidden packet on separate tensor factors
target: packet-kazhdan-commutant-placement-decouples
requires:
  - predicate-rank-jump-forces-adjoint-reynolds-gap
  - scaled-kazhdan-transport
---

On the packet adjoint factor, the Reynolds projections are precisely those of
`rho|A_f` and `rho|B_f`; on the full adjoint tensor they are amplified by the
identity on `End(H_sigma)`.  Both rank and ambient adjoint dimension are
multiplied by `dim(H_sigma)^2`, so normalized difference is unchanged.
Transport on the independent compressor factor remains exact.  Hence the two
properties coexist, proving the no-go.

