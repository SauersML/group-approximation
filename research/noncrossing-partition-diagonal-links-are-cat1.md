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
`n = 6` (HKS Theorem 4.17), `n = 7` (Jeong, arXiv:2009.09350, preprint; an exhaustive search of this lane agrees
with his Theorem 1). Open from `n = 8`.

## Attempts

- **Turning-face search (Theorem R).** In
  `research/artifacts/zp-braid-cat0-turning-face-reduction-2026-09-13.md`: if `X_m` is CAT(1) for `m < n` and no
  chain `F` of `NCP_n` has both `F` and its Kreweras dual satisfying conditions I, II, III', IV, then `X_n` is CAT(1)
  (route `diagonal-links-cat1-from-turning-face-conditions`). An exhaustive search gives no such chain for
  `n = 5, 6, 7`, and 22268 at `n = 8`, e.g. `({18} < {18, 26})`, checked by hand in
  `some-noncrossing-chain-satisfies-turning-face-conditions`. So the method as stated cannot reach `n = 8`.
- **Weakening IV with more universal pairs.** The shrinking argument of HKS Theorem 4.17 needs only some pair of
  opposite universal vertices `(v, w)` with apartments containing `F, v, w` and `C, v, w`. Opposite universal pairs
  are two cyclic intervals covering the circle and meeting in one point, and apartments are noncrossing spanning trees
  (HKS Proposition 4.4). A search of the `n = 8` candidates with all such pairs is running on MSI.
- **Using the loop geometry.** The midpoint `y` can be replaced by any point splitting the loop into two arcs shorter
  than `π`, and any turning point can serve as `x`. A condition quantified over those choices is weaker than IV and
  could exclude the remaining candidates, but it depends on the loop, not only on `F`.
