---
rg: 2
id: packet-kazhdan-commutant-placement-decouples-proof
kind: route
title: Put the compressor and a forbidden packet on separate tensor factors
target: packet-kazhdan-commutant-placement-decouples
requires:
  - predicate-rank-jump-forces-adjoint-reynolds-gap
  - scaled-kazhdan-transport
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
---

All claimed commutations are exact in the tensor-product representation.  On
the packet adjoint factor, the two Reynolds projections are precisely those
of `rho|A_f` and `rho|B_f`; on the full adjoint tensor they are amplified by
the identity on `End(H_sigma)`.  Both their rank and the ambient adjoint
dimension are multiplied by `dim(H_sigma)^2`, so the normalized difference is
unchanged.  The positive lower bound follows from the Reynolds-gap theorem.

Meanwhile every matrix sequence on the compressor factor satisfying the
scaled asymptotic-commutant hypothesis is transported exactly as before;
adjoining an independent tensor factor cannot connect it to `R_A-R_B`.  Thus
commutant placement and scaled transport alone coexist with the forbidden
packet defect, proving the no-go.
