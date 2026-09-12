---
rg: 2
id: hadamard-spectral-half-constant-conjugacy-proof
kind: route
title: Conjugate the swap dihedral group onto the Hadamard dihedral group, then join two rank-one idempotents of M_2(F_9)
target: hadamard-spectral-half-is-constant-conjugate-to-swap-idempotent
requires: []
artifacts:
  - research/artifacts/hadamard-spectral-conjugacy-and-forced-states-2026-09-12.md
---

Section 1 of the artifact.
- **Lemma 1.1:** `2x2` matrix arithmetic over `F_3` for `c = [[-1,0],[1,1]]`: `c^2 = I`, `c d c = u`,
  `c (wd) c = h`, `c w c = hu`.
- **Lemma 1.2:** conjugation by `[c]` carries `span{1_-, [w], [d], [wd]}` onto `span{1_-, [h], [u], [hu]}`, a unital
  copy of `M_2(F_3)` on which evaluation is injective.
- **Theorem 1.3:** for idempotents `p, q`, `v = pq + (1-p)(1-q)` has `vq = pv` and `v v' = v' v = 1 - (p-q)^2`.
  In the evaluation image `p = f_+ = [[-1-i,-i],[-i,-1+i]]`, `q = [[0,1],[0,1]]` and `(p-q)^2 = -I`, so `v` is a unit
  with inverse `-v'`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 9 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Re-derived independently:*
- *`c^2 = I`, `cdc = u`, `c(wd)c = h`, `cwc = hu` by hand mod 3;*
- *linear independence of `I, h, u, hu`, so evaluation is injective on the dihedral span;*
- *`v v' = 1 - (p-q)^2`, and `(p-q)^2 = -I` in `M_2(F_9)` entry by entry.*
