---
rg: 2
id: fpbs-mal-iid-chord-graphings-floor
kind: claim
title: Independent chord graphings of small mass never generate F(a,b) over K = <a, bab^-2> on the Bernoulli shift, whatever the label law
distinct_from:
  fpbs-mal-graphing-b-length-weighted-floor: that gives mass >= 1/(80 r) for all graphings with labels of double-coset b-length <= r, so iid chords with mean b-length m need mass >= 1/(80 m); this asks for a floor uniform in the label law, including laws with infinite mean b-length.
  fpbs-mal-stage-block-sprinkling-threshold: that treats sparse sprinkles of the single label b; this allows every label in F \ K, drawn independently at each point.
  fpbs-mal-bernoulli-single-stage-floor: that asks for a floor over all graphings; this is the independent subclass of its survivor P2 (factor-of-iid long chords).
artifacts:
  - research/artifacts/fpbs-iid-chord-union-bound-2026-09-19.md
  - experiments/fpbs-iid-chord-union-bound-2026-09-17/simple.py
---

**OPEN.** The route `fpbs-mal-iid-chord-graphings-floor-union-route` waits
on `fpbs-mal-simple-chain-count-uniform`.

Let `F = F(a, b)` act by the Bernoulli shift on `(Z, nu)^F`, with `nu`
non-atomic, and let `K = <a, b a b^{-2}>`. For `epsilon in (0, 1]` and a
probability `p` on `F \ K`, let `Theta(epsilon, p)` be the graphing built as
follows:
- each point is active with probability `epsilon`, independently, using a
  function of its own identity coordinate;
- an active point `z` draws `h ~ p` and carries the edge `(z, h z)`.

**Claim.** There is `epsilon_0 > 0` such that, for every `p` and every
`epsilon < epsilon_0`,

```text
E_K v Theta(epsilon, p)  ≠  E_F .
```

**Status of the pieces.**
- *Union bound (proved, artifact Lemma 1).* The probability that `x` and
  `bx` are joined is at most
  `sum_n epsilon^n sum_{D_1..D_n} prod q(D_i) N_n(D_1..D_n)`, where
  `q(D) = p(D) + p(D^{-1})`.
- *Chain count (open).* With `N_n <= rho^n` this gives
  `epsilon_0 = 1/(6 rho)`.
- *Already known.* If `p` has finite mean double-coset `b`-length `m`, the
  claim holds with `epsilon_0 = 1/(80 m)` by
  `fpbs-mal-graphing-b-length-weighted-floor`. The new content is uniformity
  over heavy-tailed label laws.

**Scope.** This is the independent subclass of the survivor P2 of
`fpbs-mal-bernoulli-single-stage-floor`. Factor-of-iid chords with shared
seeds are not covered: Lemma 1 needs independence of distinct points.
