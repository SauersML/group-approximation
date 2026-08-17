---
rg: 2
id: linton-radical-abelianization-is-truncated-group-ring-proof
kind: route
title: Lyndon's identity theorem applied to the relator supplied by Linton
target: linton-radical-abelianization-is-truncated-group-ring
requires: [linton-rational-derived-series-theorem]
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

## Direct proof

Written out in the claim.  The prerequisite supplies only the data `(r, k)` with
`w ∈ r^k[N,N]` and `R = <<r>>_G`; every step after that is separate input:

- `H = F/<<r>>` is **torsion-free**, because it is residually rationally
  solvable and such groups have torsion-free abelian rational-derived factors;
- hence `r` is **not a proper power**, by the torsion theorem for one-relator
  groups — a proper power would put torsion in `H`;
- hence **Lyndon's identity theorem** applies to `H = F/<<r>>` and makes the
  relation module `N/[N,N]` free of rank one on `[r]`;
- and then `[w] = k[r]` identifies the image of `<<w>>_F` as `kZH`, giving
  `R_ab ≅ ZH/kZH`.

Lyndon's theorem is the work here, and it needs the non-proper-power hypothesis
that the prerequisite does not state.  This is therefore not a restatement of
its single prerequisite.
