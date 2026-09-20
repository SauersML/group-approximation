---
rg: 2
id: thompson-t-padded-cover-stability-is-inert-proof
kind: route
title: Words are evaluated blockwise and are L-Lipschitz, so the defect of the corrected representation is the defect of the larger of the two blocks
target: thompson-t-padded-cover-stability-is-inert
requires:
  - thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes
  - thompson-t-lochak-schneps-presentation
---

The notation is that of the target. `||.||` is the operator norm.

**Invariant.** For a word `w` and exact pairs `x, y`, the value `w(x (+) y)` is `w(x) (+) w(y)`. So
`||w(x (+) y) - 1|| = max(||w(x) - 1||, ||w(y) - 1||)`, and taking the maximum over `r_1, r_2, r_P` gives
`D(x (+) y) = max(D(x), D(y))`.

By (L0a) of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-proof`, if `||pi(s) - psi(s)|| < eps` for
`s = a, b`, then `||r(pi) - r(psi)|| <= l(r) eps`. Hence `|D(pi) - D(psi)| <= L eps`. Apply this with
`psi = phi (+) theta`.

**Dichotomy.**
- **(i)** With `theta = 1_k`, `D(phi (+) 1_k) = D(phi) < delta`, so `D(pi) < delta + L eps`.
- **(ii)** Suppose `theta` is nontrivial.
  - By (L0c), `||theta(s) - 1|| >= sqrt 2` for `s = a` or `s = b`. So `||pi(s) - 1|| >= sqrt 2 - eps > 0`,
    and `pi` is nontrivial.
  - With `D(phi) < delta`, we have `max(D(phi), D(theta))` in `[D(theta), D(theta) + delta]`, which gives
    the stated interval.
  - If `D(pi) < c`, then `D(theta) <= D(pi) + L eps < c + L eps`. So `theta` is a nontrivial
    `(c + L eps)`-pair.

**Rounding the auxiliary block.** In Willett's Definition 1.6, `theta` is only an `eps`-representation.
Spectral rounding ((L0b) of the same proof) replaces `theta(a)` and `theta(b)` by exact elements of
orders 4 and 3. It moves them by at most `(pi/8) ||theta(a)^4 - 1||` and `(pi/6) ||theta(b)^3 - 1||`, which
are `O(eps)` when `a^4` and `b^3` lie among the controlled words. So all estimates change by `O(eps)`.

**The class.** The four listed steps produce, from a nontrivial small `phi`, an honest `pi` that is close
to `phi (+) theta`.
- If `theta` is trivial, step 2 supplies (S_T) or (S_Delta) for `phi`.
- If `theta` is nontrivial, (ii) shows that the property of `pi` used in step 4 is a property of `theta`, up
  to `delta + L eps`, whenever that property is a lower bound on `D` over nontrivial honest
  representations.
  - (R_Delta) is such a property. So is any property that `D(pi) < c` would contradict.
  - Hence step 4 either fails or is already witnessed by `theta`, and `phi` plays no role.

The quoted passages of arXiv:2408.13350 (Definition 1.6, Remark 1.13, Section 1.7) are cited as in the
target. They show that the available theorems give `theta` with no control, so they fall under (ii).
