---
rg: 2
id: radu-mark-is-controlled-by-one-commutator-proof
kind: route
title: Run Lemma 3.5 with bi-invariant error bookkeeping
target: radu-mark-is-controlled-by-one-commutator
requires: []
artifacts:
  - research/artifacts/titz-witzel-radu-sublattice-2026-09-11.md
---

Bi-invariance gives:

* `d(g,h) = d(1, g^(-1)h)`;
* invariance under conjugation and inversion;
* `d(g1 g2, h1 h2) <= d(g1,h1) + d(g2,h2)`.

Cyclic rotations of a relator are conjugates, so they have the same defect.

1. From the relators: `d(za, bz) = d(zb, az) = e3`, `d(xa, ax) = e1`,
   `d(ya, ay) = e2`, `d(xb, bx) = e4`, `d(yb, cy) = d(yc, by) = e5` and
   `d(xc, cz) = d(zc, cx) = e6`.  For example `(za)^(-1)(bz) = azbz`, and
   `(zc)^(-1)(cx) = czcx` is a rotation of `cxcz`.
2. `delta a = xza ~ xbz ~ bxz` gives `d(delta a, b delta) <= e3 + e4`.
   Likewise `d(delta b, a delta) <= e1 + e3`.  `delta c = xzc ~ xcx ~ czx`
   gives `d(delta c, c delta^(-1)) <= 2e6`, hence
   `d(delta^2 c, c delta^(-2)) <= 4e6` and
   `d(delta^2 a, a delta^2) <= e1 + 2e3 + e4`.
3. `ub = y delta^2 yb ~ y delta^2 cy ~ yc delta^(-2) y ~ by delta^(-2) y = bu^(-1)`,
   so `d(ub, bu^(-1)) <= eta := 2e5 + 4e6`.
4. `au = a y delta^2 y ~ y a delta^2 y ~ y delta^2 a y ~ ua`, so
   `d(au, ua) <= lambda := e1 + 2e2 + 2e3 + e4`.
5. `d(delta u b delta^(-1), delta b u^(-1) delta^(-1)) <= eta`.
   * `delta u b delta^(-1) ~ u delta b delta^(-1) ~ ua` costs at most
     `kappa1 + e1 + e3`.
   * `delta b u^(-1) delta^(-1) ~ a delta u^(-1) delta^(-1) ~ au^(-1)` costs at
     most `e1 + e3 + kappa1`, because `[delta, u^(-1)]` is conjugate to the
     inverse of `[u, delta]`.
   * Hence `d(ua, au^(-1)) <= eta + 2 kappa1 + 2e1 + 2e3`.
6. `d(delta^4,1) = d(u^2,1) = d(au, au^(-1)) <= d(au, ua) + d(ua, au^(-1))`,
   which is `(RL1)`.
7. With `w = delta b`: `d(aw, delta) = d(delta b, a delta) <= e1 + e3`, so
   * `kappa1 = d(u delta, delta u) <= 2(e1+e3) + d(u aw, aw u)`;
   * `d(u aw, aw u) <= d(ua, au) + d(uw, wu) = lambda + kappa2`;
   * so `kappa1 <= kappa2 + 3e1 + 2e2 + 4e3 + e4`.

   The symmetric computation bounds `kappa2` by `kappa1` plus the same
   quantity.  This is `(RL2)`, and inserting it into `(RL1)` gives `(RL3)`.

At zero defects the two commutators of Titz Mite--Witzel Proposition
3.4(4) vanish together, and either one kills the mark, recovering Lemma 3.5.
