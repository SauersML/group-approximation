---
rg: 2
id: pure-braided-bht-sigma-invariants-miss-only-endpoint-hull
kind: claim
title: "Every BNSR invariant of bF_{n,r} misses only characters pulled back from the endpoint germs of F_{n,r}"
distinct_from:
  zaremsky-2-13-bnsr-of-pure-braided-bht-groups: that claim is the question itself; this is one candidate answer, a specific formula for Sigma^m(bF_{n,r}).
---

Candidate answer to Zaremsky Problem 2.13. For all `n >= 2` and `r >= 1`,
write `pi: bF_{n,r} -> F_{n,r}` for the forgetful map and `chi_0`, `chi_1` for
the first- and last-leaf depth characters of `F_{n,r}` (Zaremsky,
arXiv:1502.02620; up to sign, the log base `n` of the slopes at the two
endpoints). `Hom(bF_{n,r}, R)` has rank `n^2`
(`pure-braided-bht-braid-characters-dimension-n-n-minus-1`). Then:

1. `[chi] notin Sigma^1(bF_{n,r})` iff `[chi]` is `[chi_0 o pi]` or
   `[chi_1 o pi]`;
2. for `m >= 2`, `[chi] notin Sigma^m(bF_{n,r})` iff
   `chi = (a chi_0 + b chi_1) o pi` with `a, b >= 0` (not both zero).

So every character with a nonzero component on the pure braid kernel, and
every character pulled back from `F_{n,r}` that `Sigma^m(F_{n,r})` contains,
lies in `Sigma^infinity(bF_{n,r})`.

This is the `n`-ary, `r`-root form of Zaremsky's computation for `F_br`
(arXiv:1403.8132; arXiv:1803.02717, Theorem 5.1), combined with his
computation for `F_{n,infinity}` (arXiv:1502.02620, Theorem A).

## Attempts

- 2026-09-13, split into parts by route `pure-braided-bht-sigma-formula-from-parts`:
  - proved (unreviewed): the character splitting and rank `n^2`;
  - proved (unreviewed): characters whose braid part is nonzero on large full
    twists lie in `Sigma^infinity`;
  - proved (unreviewed): holes of `F_{n,r}` pull back, and for `m >= 2` the
    endpoint hull is a hole for every `r` (`F_{n,r} ≅ F_{n,1}` preserving
    endpoint characters);
  - proved (unreviewed), `Sigma^1`: every braid-nonzero character, and every
    pulled-back character off `span(chi_0, chi_1)`, lies in `Sigma^1`;
  - open: `Sigma^m` for `m >= 2` of braid parts in the
    `(n(n-1) - 2)`-dimensional full-twist-invisible subspace (`n >= 3` only),
    reduced to BNSR invariants of pure braid groups;
  - open: pulled-back characters outside the hull lift to `Sigma^m` (`m >= 2`),
    and for `Sigma^1` the circle `span(chi_0, chi_1)` apart from the endpoints.
- For `n = 2`, `r = 1` the formula is Zaremsky's theorem, so the open content is
  `n >= 3` or `r >= 2`.
