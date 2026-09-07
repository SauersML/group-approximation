---
rg: 2
id: split-ca-defect-rank-proof
kind: route
title: Recover each translated inverse defect by bounded maps on finite orbit modules
target: split-ca-defects-force-linear-observable-rank
requires: []
artifacts:
  - research/artifacts/gottschalk-observable-growth-2026-09-07.md
  - research/artifacts/check-gottschalk-observable-growth-2026-09-07.py
  - research/artifacts/gottschalk-observable-growth-replay-2026-09-07.json
---

Sections 1–5 of the artifact give the complete argument. A finite
nonconstant pattern has finite stabilizer H, so its orbit completion is
ell^2(G/H), a finite Hilbert G-module of dimension 1/|H|.

TS=I gives E^2=E, TE=0, and ES=0. A nonzero reverse error on a one-site
observable remains nonzero modulo constants, since it vanishes on the
nonempty encoder image. Faithful trace therefore makes delta positive
exactly in the nonsurjective case.

The identities E T^i S^j theta = delta_(i,j) theta produce two bounded
factorizations: diag(theta) factors through Phi_n=sum_j S^j theta, and
Phi_n factors through diag(theta). All source and target modules at a
fixed n contain only finitely many whole pattern orbits; projection back
to the seed's containing module makes the recovery maps well typed.
Rank monotonicity in both directions gives rank_G Phi_n=n delta.
The image lies in V_(n+1), yielding the claimed bound and criterion.

The dimension facts are standard finite-trace facts, cited and explained
in Section 2. This is a mathematical proof route, not a declaration of
Lean kernel verification; the computation is a separately scoped replay.
