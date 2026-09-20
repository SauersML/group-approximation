---
rg: 2
id: bf-n-r-pulled-back-sigma-m-lifts-off-endpoint-hull
kind: claim
title: "For m >= 2, a pulled-back character of bF_{n,r} off the nonnegative endpoint hull lies in Sigma^m"
distinct_from:
  bf-n-r-pulled-back-characters-follow-endpoint-hull: that open claim is the two-sided formula for every m; this is exactly its one remaining direction, m >= 2 membership.
  bf-n-r-pulled-back-sigma-one-misses-only-endpoint-characters: that claim is the m = 1 case.
---

For `n >= 2`, `r >= 1`, `m >= 2` and nonzero `psi` in `Hom(F_{n,r}, R)` not of the
form `a chi_0 + b chi_1` with `a, b >= 0`, `[psi o pi]` lies in
`Sigma^m(bF_{n,r})`. Equivalently, `Sigma^m` membership lifts along the split
quotient `pi`, given Zaremsky's formula for `Sigma^m(F_{n,r})`.

## Attempts

- 2026-09-20 (swarm-0917, host-geometry). Open. Pulled-back characters vanish
  on every cell stabilizer of the Stein space, so Meinert's criterion does not apply.
  The connected-and-dominating trick that settles `m = 1` has no higher analogue to cite.
  Two routes and their gaps are in
  `research/artifacts/zp-bf-n-r-sigma1-pullbacks-2026-09-20.md` §6:
  - Morse theory with `(chi, f)`: Zaremsky's Lemma 5.5 fails for braided linear disks. Restricted foot
    sets are already handled by Skipper–Wu Theorem 4.13.
  - Ascending HNN over deferred subgroups (the `Sigma^m` version of BGK Theorem 2.3 follows from MMV
    Theorem 2.4 on the Bass–Serre tree). It needs `F_infinity` for the `n`-ary deferred subgroups, that is,
    contractibility of a restricted Stein complex.
