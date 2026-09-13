---
rg: 2
id: some-gl-n-z-does-not-embed-in-2v
kind: claim
title: Some GL_n(Z) does not embed in the Brin-Thompson group 2V
distinct_from:
  every-gl-n-z-embeds-in-2v: that is the affirmative answer to Zaremsky 2.19(d); this is its negation.
  some-gl-n-z-embeds-in-no-brin-thompson-group: that excludes GL_n(Z) from every mV at once; this excludes it from 2V only, so it is implied by that claim.
  zaremsky-2-19d-every-gl-n-z-in-2v-resolved: that claim is Zaremsky's question 2.19(d); this claim is its negative answer.
---

There is `n` (necessarily `n >= 3`) such that `GL_n(Z)` is not isomorphic to any
subgroup of `2V`. It follows from `some-gl-n-z-embeds-in-no-brin-thompson-group`
through `some-gl-n-z-not-in-2v-from-no-nv`.

## Attempts

- 2026-09-13 (lane z2-19-glnz-q-2v, unreviewed): **undistortion is dead.** `2V`
  contains a distortion element (`brin-thompson-mv-contains-a-distortion-element`),
  so the argument that excludes `H_3(Z)` from `V` does not apply.
- 2026-09-13, same lane: **most promising obstruction: a right-angled Artin
  subgroup.**
  - Belk–Bleak–Matucci (arXiv:1602.08635, Conjecture 1.7) predict that
    `Z^3 * Z` does not embed in `2V`; for `V` the analogue `Z^2 * Z` is a theorem
    of Bleak–Salazar-Díaz.
  - `Z^3 * Z <= GL_8(Z)` (`z3-free-z-embeds-in-gl8z`). So the conjecture for
    `2V`, recorded as the open claim `z3-free-z-does-not-embed-in-2v`, gives this
    claim through `some-gl-n-z-not-in-2v-via-z3-free-z`.
  - Next target: `z3-free-z-does-not-embed-in-2v`.
- The Haagerup property of `2V`, or finiteness of its Kazhdan subgroups, would
  also give this claim through `SL_3(Z)` (Problem 2.7).
