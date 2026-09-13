---
rg: 2
id: almost-commuting-higman-collapse-proof
kind: route
title: Transport the relation c^b = c^2 by an almost-central a to get c^2 close to c^4, then walk around the cycle
target: almost-commuting-opposite-higman-generators-force-collapse
requires: []
artifacts:
  - research/artifacts/solve-higman-sofic-2026-09-13.md
---

**Tools.** Bi-invariance gives the following, used throughout:
- `rho(gxh, gyh) = rho(x, y)`;
- `rho(xy, x'y') <= rho(x, x') + rho(y, y')`;
- `rho(x^-1, y^-1) = rho(x, y)`;
- `l(g^-1 x g) = l(x)`.

**Step 1.** `rho(a^-1 c a, c) = rho(ca, ac) <= eta`, hence
`rho(a^-1 c^2 a, c^2) <= 2 eta`.

**Step 2.** `rho(a^-1 (b^-1 c b) a, a^-1 c^2 a) = rho(b^-1 c b, c^2) <= delta`.

**Step 3.** Write `a^-1 b^-1 c b a = (a^-1 b a)^-1 (a^-1 c a) (a^-1 b a)`. Compare
it factor by factor with `b^-2 c b^2`:

```text
rho(a^-1 b^-1 c b a, b^-2 c b^2) <= delta + eta + delta.
```

**Step 4.** `b^-2 c b^2 = b^-1 (b^-1 c b) b` is within `delta` of
`b^-1 c^2 b = (b^-1 c b)^2`, and that is within `2 delta` of `c^4`. So
`rho(b^-2 c b^2, c^4) <= 3 delta`.

**Step 5.** Chain Steps 4, 3, 2 and 1:

```text
l(c^2) = rho(c^4, c^2) <= 3 delta + (2 delta + eta) + delta + 2 eta = 6 delta + 3 eta.
```

**Step 6.** `l(c) = l(b^-1 c b) <= rho(b^-1 c b, c^2) + l(c^2) <= 7 delta + 3 eta`.

**Step 7 (around the cycle).**
- If `rho(c^-1 e c, e^2) <= delta`, then
  `l(e) = rho(e^2, e) <= delta + rho(c^-1 e c, e) = delta + rho(ec, ce) <= delta + 2 l(c)`.
  So `l(e) <= 15 delta + 6 eta`.
- In the same way `l(a) <= delta + 2 l(e) <= 31 delta + 12 eta`.
- And `l(b) <= delta + 2 l(a) <= 63 delta + 24 eta`.
