---
rg: 2
id: noncrossing-partition-diagonal-links-are-cat1
kind: claim
title: For every n the diagonal link of the noncrossing partition complex is CAT(1)
distinct_from:
  every-braid-group-is-cat0: that claim is about braid groups acting on CAT(0) spaces; this one is the curvature statement about the complexes |NCP_n| that implies it (Brady–McCammond's conjecture)
---

For every `n >= 3`, the diagonal link `X_n = LK(e_01, |NCP_n|)` of the orthoscheme complex of the
noncrossing-partition lattice, with the spherical orthoscheme metric, is CAT(1). By Brady–McCammond this makes every
`|NCP_n|` CAT(0) and every braid group CAT(0) (route `every-braid-group-is-cat0-via-diagonal-links`); Brady–McCammond
conjecture that braid groups are CAT(0) (their Conjecture 8.4, as cited by HKS).

Known: `n = 3, 4` directly (HKS Remark 4.1), `n = 5` (Brady–McCammond, computer-assisted; HKS Corollary 4.11 by hand),
`n = 6` (HKS Theorem 4.17), `n = 7` (Jeong, arXiv:2009.09350, preprint).

## Attempts

- **Turning-face search.** Theorem R in
  `research/artifacts/zp-braid-cat0-turning-face-reduction-2026-09-13.md`: if `X_m` is CAT(1) for `m < n` and no
  chain `F` of `NCP_n` has both `F` and its Kreweras dual satisfying conditions I, II, III', IV, then `X_n` is CAT(1).
  So each `n` is a finite check (route `diagonal-links-cat1-from-turning-face-conditions`). A mechanical check for
  `n <= 8` is in progress.
- If some `n` has chains satisfying all four conditions, the method is inconclusive at that `n`. What remains is
  the specific chamber through the loop's midpoint, not every chamber, which is weaker than IV.
