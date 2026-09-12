---
rg: 2
id: sylvester-rank-functions-from-weakly-finite-images
kind: route
title: A state gives a weakly finite image with faithful states; a rank function on that image pulls back to the summand
target: ternary-anti-central-states-give-sylvester-rank-functions
requires: [anti-central-rank-condition-gives-weakly-finite-image, anti-central-weakly-finite-images-carry-rank-functions]
artifacts:
  - research/artifacts/state-upgrade-rank-condition-gap-2026-09-12.md
---

Artifact Sections 3–4.
1. **(U1a).** A state on `(K_0(S_-), [eps_-])` gives a quotient `W = S_-/J`, established in the first
   requirement. `W` is nonzero and weakly finite, every state on it is faithful on idempotent matrices,
   and `G_3` embeds with `z -> -1`.
2. **(U1b).** By the second requirement, `W` carries a Sylvester matrix rank function `N_W` with
   `N_W(1) = 1`.
3. **Pullback.** `N(X) = N_W(X + M(J))` is a Sylvester matrix rank function on `S_-` with `N(eps_-) = 1`.

So (U1) reduces to (U1b), and (U1a) is no longer open.
