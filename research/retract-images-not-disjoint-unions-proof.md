---
rg: 2
id: retract-images-not-disjoint-unions-proof
kind: route
title: Glue preimages of a point from each piece far apart and apply the retraction
target: retract-images-of-full-shifts-are-not-disjoint-unions
requires: []
artifacts:
  - research/artifacts/automaton-monoid-intrinsic-sizes-2026-09-12.md
  - research/artifacts/w3-vf-positive-verification-2026-09-12.md
---

Proposition 4.1 of the artifact.

- **A finite window decides the piece:** `X_1` is clopen in `X`, so `x in X_1` iff `x|_W in P` for a
  finite `W` and a set `P` of patterns.
- **Separate the windows:** since `G` is infinite there is `g` with `W M ∩ g W M` empty, where `M` is
  the memory of `f`.
- **Glue:** take `y in X_1`, `z in X_2` with `f`-preimages `y'`, `z'`. Let `w` equal `y'` on `W M` and
  `g.z'` on `g W M`. By locality and equivariance, `x = f(w)` agrees with `y` on `W` and with `g.z` on
  `g W`.
- **Contradiction:** `x in X_1`, while `(g^-1.x)|_W = z|_W` puts `g^-1.x` in `X_2`, hence `x in X_2`.

**Verification.** `w3-vf-positive` passed this route (Section 6.4 of `research/artifacts/w3-vf-positive-verification-2026-09-12.md`).
