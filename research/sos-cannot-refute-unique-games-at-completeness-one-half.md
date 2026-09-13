---
rg: 2
id: sos-cannot-refute-unique-games-at-completeness-one-half
kind: claim
title: For every eps there is c > 0 such that degree-N^c SoS has pseudo-value >= (1-eps)/2 on some N-vertex unique games of value <= eps
distinct_from:
  unique-games-hard-at-completeness-one-half: that is NP-hardness at completeness one half; this is the unconditional SoS integrality-gap statement one would get by pushing a Grigoriev pseudo-solution through the same reduction.
  sd-rich-and-unique-games-sos-gaps-interconvert: that transfers SoS gaps between UG and admissible 2-to-1 games at matched degree; this asks for a polynomial-degree UG gap itself at completeness one half.
---

**OPEN.** For every `eps > 0` there are `c = c(eps) > 0` and linear unique game
instances `U_N` on `N` vertices with `val(U_N) <= eps` whose degree-`N^c`
sum-of-squares relaxation has value at least `(1-eps)/2`.

If true, it is an unconditional reason why any refuting algorithm
(`unique-games-gap-admits-polynomial-time-algorithm`) must use completeness near
`1`, even inside the SoS hierarchy. The NP-hardness in
`unique-games-hard-at-completeness-one-half` gives the same conclusion only
conditionally on `P != NP`.

## Attempts

* **Tulsiani-style transfer through the 2-to-2 reduction.** Start from random
  3-XOR on `n` variables with `O(n)` clauses. By Grigoriev, it has a degree-`Omega(n)`
  pseudo-distribution satisfying every equation [recalled]; by a union bound,
  its value is at most `1/2 + delta` w.h.p. [recalled]. Apply the reduction
  behind `two-to-two-games-theorem`: outer smooth label cover with `t`-fold
  repetition, then Grassmann encoding of the linear assignment. Honest labels
  depend on `O(t)` source variables, so the pseudo-distribution pushes forward
  at degree `Omega(n)/O(t)`. Split constraints as in
  `unique-games-hard-at-completeness-one-half`. **Where it may die (unchecked):**
  (i) completeness must follow from the local 3-XOR equations by a low-degree
  polynomial identity, and the smoothing and zoom steps have to be checked;
  (ii) KMS soundness must apply to random source instances, not only to
  PCP-produced ones; (iii) the size is `n^(O(t))` with `t = poly(1/eps)`, so the
  exponent `c` degrades with `eps`. No step of KMS's completeness proof was read
  here.
* **Literature.** A bounded web search on 2026-09-12 did not locate this
  statement. It may be folklore; this is not a novelty claim.
