---
rg: 2
id: site-pullbacks-strict-iff-stabilizer-self-compressed-proof
kind: route
title: Equivariance pins the one read site to a coset fixed by the stabilizer, and fibres of the site map decide surjectivity
target: site-pullbacks-strict-iff-stabilizer-self-compressed
requires: []
artifacts:
  - research/artifacts/simple-host-direct-attack-2026-09-12.md
---

Section 1 of the artifact.

1. An equivariant site map is determined by `psi(K) = cK`. It is well defined iff
   `c^-1 K c <= K`, always onto, and injective iff `c K c^-1 = K`.
2. For a one-site map `F(y)(o) = theta(y(p))` with `theta` nonconstant, invariance of the base
   point under `K` forces `K` to fix `p`, so `p = cK` with `c^-1 K c <= K`.
3. The pullback `y -> y o psi_c` is injective because `psi_c` is onto. It is onto iff `psi_c` is
   injective, since the two points of a nontrivial fibre carry equal values in every image.
4. A finite `K` has no proper conjugate into itself.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 13 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`).
