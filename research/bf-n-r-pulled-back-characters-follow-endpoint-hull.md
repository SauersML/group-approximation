---
rg: 2
id: bf-n-r-pulled-back-characters-follow-endpoint-hull
kind: claim
title: "A character of bF_{n,r} pulled back from F_{n,r} misses Sigma^m exactly on the endpoint characters (m = 1) or their nonnegative hull (m >= 2)"
distinct_from:
  bf-n-r-sigma-m-holes-of-f-n-r-pull-back: that proved claim is one direction and one residue class of r; this open claim is the full two-sided statement for every r.
---

For `n >= 2`, `r >= 1` and `psi` in `Hom(F_{n,r}, R)`:

- `[psi o pi]` is not in `Sigma^1(bF_{n,r})` iff `[psi]` is `[chi_0]` or `[chi_1]`;
- for `m >= 2`, `[psi o pi]` is not in `Sigma^m(bF_{n,r})` iff
  `psi = a chi_0 + b chi_1` with `a, b >= 0`.

Here `chi_0, chi_1` are the first- and last-leaf depth characters (Zaremsky,
arXiv:1502.02620).

## Attempts

- Proved half: holes pull back, and for `r ≡ 1 mod (n-1)` the endpoint hull is
  a hole for `m >= 2` (`bf-n-r-sigma-m-holes-of-f-n-r-pull-back`).
- `n = 2`, `r = 1`: all of it is Zaremsky's (arXiv:1403.8132 Theorem 3.4;
  arXiv:1803.02717 Theorem 5.1).
- Open: (a) `Sigma^m(F_{n,r})` for `r ≢ 1 mod (n-1)`. Candidate route: Brown's
  isomorphism `F_{n,r} ≅ F_{n,infinity}`, to be verified together with what it
  does to `chi_1`. (b) Lifting: a pulled-back `chi` vanishes on every cell
  stabilizer, so Meinert's criterion is unavailable. Plan: Morse theory with
  `(chi, f)` on the Skipper–Wu Stein space, as in Zaremsky's proof of Theorem A
  for `F_n`, with the `(n-1)`-matching complexes replaced by linear arc matching
  complexes on restricted foot sets; or ascending HNN decompositions over
  deferred subgroups generalizing Case 3 of arXiv:1803.02717 Theorem 5.1.
