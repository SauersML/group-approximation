---
rg: 2
id: anti-central-rank-functions-from-certificate-flattening
kind: route
title: If triangular identity certificates over the anti-central summand flatten to minor certificates, its states give Sylvester rank functions
target: ternary-anti-central-states-give-sylvester-rank-functions
requires: [anti-central-triangular-certificates-flatten-to-minors, sylvester-rank-functions-iff-no-triangular-certificate]
artifacts:
  - research/artifacts/gottschalk-region-synthesis-2026-09-12.md
---

Wiring. `anti-central-triangular-certificates-flatten-to-minors` was landed in c1b9da39b as the certificate
form of step (U1), but no route led out of it. This is that route.

1. Let `S_- = eps_- F_3[G_3]`, a unital ring with unit `eps_-`, and suppose `(K_0(S_-), [eps_-])` has a state.
2. By part 2 of `sylvester-rank-functions-iff-no-triangular-certificate`, `S_-` has the rank condition, so no
   minor certificate `I_(q+1) <~ I_q` exists over `S_-`.
3. By the first requirement, any triangular certificate `I_(q+1) <=_T I_q` over `S_-` flattens to a minor
   certificate. So none exists.
4. By part 1 of the criterion, `S_-` carries a Sylvester matrix rank function `N`. It has
   `N(I_1) = N(eps_-) = 1`, which is the conclusion of `ternary-anti-central-states-give-sylvester-rank-functions`.

This runs parallel to `sylvester-rank-functions-from-weakly-finite-images` (via U1b). Either open lemma gives (U1).
