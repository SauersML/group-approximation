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
the characters of `F_{n,r}` given by the log base `n` of the slope at the left
and right endpoints (conventions as in Zaremsky, arXiv:1502.02620). Then:

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

- 2026-09-13: open. Needed pieces: (a) a basis of `Hom(bF_{n,r}, R)`;
  (b) characters nonzero on the braid kernel lie in `Sigma^infinity`;
  (c) pulled-back characters follow `Sigma^m(F_{n,r})` on both sides; (d) the
  identification of `Sigma^m(F_{n,r})` for finite `r` with the `F_{n,infinity}`
  formula. For `F_br`, (b) and (c) come from a CAT(0) Stein–Farley complex,
  Morse theory, central-element and HNN-decomposition criteria. Whether
  those arguments survive the residue-mod-`(n-1)` braid characters that
  appear for `n >= 3` is the crux.
