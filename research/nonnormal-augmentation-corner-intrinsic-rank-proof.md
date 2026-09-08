---
rg: 2
id: nonnormal-augmentation-corner-intrinsic-rank-proof
kind: route
title: Map the surviving corner to its own tracial matrix ultraproduct and use the finite average identity
target: nonhyperlinear-finite-augmentation-corner-kills-mf
requires:
  - matrix-corona-projection-ideal-and-corner-calculus
artifacts:
  - research/artifacts/nonnormal-finite-augmentation-corner-endgame-2026-09-08.md
---

Extend any corona homomorphism `theta` linearly to the group algebra.
If `p=theta(q)` is nonzero, the prerequisite identifies `pQ_dp`
with a norm matrix corona in dimensions `rank(p_n)` along its
nonzero coordinates. The further quotient to any tracial matrix
ultraproduct is unital because operator-norm null sequences are
null for these normalized Hilbert--Schmidt norms. Composing with
the given algebra map produces a CE tracial state, a contradiction.
Hence `theta(q)=0`.

For `q=1-e_K`, one has `theta(e_K)=1` and `k e_K=e_K` for every
`k in K`, so `theta(k)=1`. The argument never requires `K` normal
or the whole group to preserve the lifted matrix corner. It uses
only the corner algebra and a finite-group averaging identity.
