---
rg: 2
id: stw99-ii1-awstar-dimension-is-non-pathological
kind: claim
title: In every II_1 AW*-factor, weighted projection covers of 1 have dimension mass bounded below by a fixed delta > 0
distinct_from:
  stw01-quasitrace-crux-is-awstar-factor-w-star: that asks for a large W*-corner; this asks only for a lower bound delta > 0, however small, on the dimension mass of finite weighted projection covers, with no operator-algebraic conclusion demanded.
  stw99-quasitrace-minorant-zero-one-law: that proves the dichotomy mass 0 or 1; this is the open assertion that mass 0 never occurs.
---

Let `M` be a type `II_1` AW*-factor with dimension function `D`. Claim: there is
`delta > 0` with

```text
c_i >= 0, p_i projections, sum_{i<=N} c_i p_i >= 1   ⟹   sum_i c_i D(p_i) >= delta.
```

Equivalently, `D` is non-pathological: it dominates a nonzero positive linear
functional on projections.

**Status.** OPEN. By `stw99-quasitrace-minorant-zero-one-law` this is equivalent
to `M` being W*, and it holds for all `M` iff Problem I holds. Its value is its
form. It is a single one-sided linear inequality with an arbitrary constant, for
finitely many projections, and it contains no linearity, no normality and no
completeness.

Known constraints:

- Covers by pairwise commuting projections have mass `>= 1`.
- Covers splitting into `k` commuting classes have mass `>= 1/k`, from Haagerup's
  square-root subadditivity.
- A violating family needs unboundedly many noncommuting classes.

## Attempts

- *Noncommutative Kalton–Roberts* (exhaustive additive measure ⟹ non-pathological).
  The commutative theorem uses Boolean combinatorics that has no analogue for
  noncommuting projections. The II_1 Gleason step uses a trace. Dies there.
