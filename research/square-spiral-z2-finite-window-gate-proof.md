---
rg: 2
id: square-spiral-z2-finite-window-gate-proof
kind: route
title: Four-piece translation structure plus diagonal invariance reduces the window identities to one exact ring check
target: square-spiral-z2-enumeration-passes-the-finite-window-gate
requires:
  - shell-ascending-gate-is-a-finite-window-inclusion
artifacts:
  - research/artifacts/hl-bh-universal-2-2026-09-13.md
  - research/artifacts/hl-bh-universal-2-2026-09-13/spiral_common.py
  - research/artifacts/hl-bh-universal-2-2026-09-13/spiral_verify.py
  - research/artifacts/hl-bh-universal-2-2026-09-13/verify.json
---

Notation as in the claim. `rad(p) = max(|x|, |y|)`.

**Step 1. `sigma` is the four-piece translation.**
- **Sides.** Read the traversal of ring `r`:
  - right side `(r, y)`, `-r+1 <= y <= r-1`, steps `+e2`, and lies in `R`;
  - top side `(x, r)`, `-r+1 <= x <= r-1`, steps `-e1`, and lies in `T`;
  - left side `(-r, y)` steps `-e2`, and lies in `Lf`;
  - bottom side `(x, -r)` steps `+e1`, and lies in `B`.
- **Corners and origin.** `(r, r)` steps `-e1` (in `T`); `(-r, r)` steps `-e2` (in `Lf`);
  `(-r, -r)` steps `+e1` (in `B`); `(r, -r)` steps `+e1` to `(r+1, -r)`, the first point of
  ring `r+1` (in `B`). The origin steps to `(1, 0)` (in `B`).
- **Partition.** Each point satisfies exactly one of the four defining conditions: the
  corners are separated by the strict inequalities.
- **Check.** `verify.json` reports zero mismatches of this formula over all points of
  radius at most 149.

**Step 2. Pieces are decided by two signs, and travel is bounded.**
- **Signs.** Put `a = x - y` and `b = x + y`. Then:
  - `R = {a > 0, b > 0}`;
  - `T = {a <= 0, b > 0}`;
  - `Lf = {a < 0, b <= 0}`;
  - `B = {a >= 0, b <= 0}`.
  So `sigma(p)` depends only on the signs of `a(p)` and `b(p)`, with the ties as displayed.
- **Travel.** Evaluating either word, or `sigma^-1 L_g sigma`, applies at most 25 letters.
  Each letter moves a point by at most 2 in the sup norm, so it changes `a` and `b` by at
  most 4. Along any evaluation chain, `a` and `b` change by at most 100.

**Step 3. Off the diagonal strips nothing happens.**
- **Setup.** If `|a(p)| > 100` and `|b(p)| > 100`, every point of the evaluation chain has
  the same strict signs of `a` and `b`, hence lies in the same piece.
- **Consequence.** There `sigma^(+-1)` acts as one fixed translation, all letters commute,
  and both words and `sigma^-1 L_g sigma` send `p` to `p + g`.

**Step 4. Invariance along each diagonal strip.**
- **The strip `|a| <= 100`, `b > 200`.** Every chain point has `b > 100`. So the piece of
  each chain point is decided by the sign of `a` alone. Translation by `tau = (1,1)` fixes
  `a` and increases `b`. So `sigma^(+-1)` commutes with `tau` at every chain point, and
  translations commute with `tau`. Hence `w(tau p) = tau w(p)` for both words and for
  `sigma^-1 L_g sigma`, and the mismatch set of this strip is `tau`-invariant.
- **The other halves.** The same holds for `|a| <= 100`, `b < -200` with `tau = (-1,-1)`,
  and for `|b| <= 100`, `a > 200` or `a < -200` with `tau = (1,-1)` or `(-1,1)`.
- **Fundamental domains.** Each `tau`-orbit in a strip half meets the cross-section where
  `|b|` (respectively `|a|`) is 201 or 202. That cross-section has radius at most 151.
- **What remains.** The points not covered by Steps 3–4 satisfy `|a|, |b| <= 200`, a
  finite set.

**Step 5. Exact finite check.**
- **What was run.** `spiral_verify.py`, with `RMAX=240` on MSI, evaluates both words and
  `sigma^-1 L_g sigma` pointwise on every point of radius 40 to 228 (202608 points). Every
  chain stays inside the enumerated box.
- **Result.** `verify.json`: `piece_formula_mismatches: 0`, `word_e1_mismatches: 0`,
  `word_e2_mismatches: 0`.
- **Conclusion.** All four strip cross-sections lie in this annulus, so by Step 4 both
  identities hold on the four strip halves. Step 3 gives them off the strips. So they hold
  at all but finitely many points.

**Step 6. Transport and conclusion.**
- **Transport.** Conjugation by `nu` carries `L_g` to `lambda_g` and `sigma` to `s`, and
  preserves "at all but finitely many points". `delta_j(h)` and `T_k(delta_j(h))` are words
  in `lambda(P)` and `s^j lambda(P) s^-j` with `j` in `{0, 1, 2}`. So
  `s^-1 lambda_g s <= W_2` for `g = e1, e2`.
- **Conclusion.** `shell-ascending-gate-is-a-finite-window-inclusion` (with `eps = 1`,
  `N = 2`) gives the gate with `B = W_2`.
