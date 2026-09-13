---
rg: 2
id: every-gl-n-z-embeds-in-2v
kind: claim
title: Every GL_n(Z) embeds in the Brin-Thompson group 2V
distinct_from:
  every-gl-n-z-embeds-in-some-brin-thompson-group: that allows the dimension m of mV to grow with n; this fixes m = 2, so it implies that claim.
  zaremsky-2-19d-every-gl-n-z-in-2v-resolved: that claim is Zaremsky's question 2.19(d); this claim is its affirmative answer.
---

For every `n >= 1`, `GL_n(Z)` is isomorphic to a subgroup of `2V`.
Equivalently, a finite-index subgroup of `SL_n(Z)` embeds in `2V` for every `n`.
It implies `every-gl-n-z-embeds-in-some-brin-thompson-group` through
`every-gl-n-z-in-some-nv-from-2v`.

## Attempts

- 2026-09-13 (lane z2-19-glnz-q-2v, unreviewed): `n <= 2` holds, since `GL_2(Z)`
  embeds in `V <= 2V`.
- For `n >= 3`, `2V` would contain `H_3(Z)` and the infinite Kazhdan group
  `SL_3(Z)`. That needs a drift-free central element, which exists in `2V`
  (`brin-thompson-mv-contains-a-distortion-element`, m = 2), and it needs `2V` to
  fail the Haagerup property.
- Every RAAG sits in some `GL_N(Z)`, so this claim puts every RAAG in `2V`. That
  contradicts the Belk–Bleak–Matucci conjecture that `Z^3 * Z` does not embed in
  `2V` (arXiv:1602.08635, Conjecture 1.7). A proof of that conjecture for
  `m = 2` would refute this claim. The statement that all RAAGs embed in some
  `GL_N(Z)` (Davis–Januszkiewicz embedding in right-angled Coxeter groups plus
  the integral Tits representation) was not re-read.
