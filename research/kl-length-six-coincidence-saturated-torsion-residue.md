---
rg: 2
id: kl-length-six-coincidence-saturated-torsion-residue
kind: claim
title: The coincidence-saturated length-six words with a torsion sign-change coefficient inject over every group
distinct_from:
  kl-length-six-one-coincidence-words-inject: that settles exactly one coincidence under conditions on the light cycle; this is the open statement for at least two coincidences, where every weight test with involution loops is impossible.
  kl-even-syllable-words-reduce-to-shorter-equations: that settles the two families lying in G * <t^2> by substitution; this is the open residue after those families are removed.
  kl-sign-index-two-infinite-order-loops-inject: that removes every case with both sign-change coefficients of infinite order; this concerns the torsion case that theorem leaves.
---

Let `G` be any group and `w` cyclically reduced, not a proper power, of variable
length six and class `+++++-` or `++++--`, with at least one sign-change
coefficient of finite order. Normalize by the shift `t -> s c^(-1)` of
`kl-even-syllable-reduction-proof`, and write the same-sign labels in run order.

**Residue shapes** (`g != 1`, loops `y` at `t^-` and `x` at `t^+`, at least one
of finite order):
- `+++++-`, P-labels normalized so a repeated label is `1`:
  - all four equal: `(1,1,1,1)`, i.e. `w = t^5 y t^(-1) x`;
  - three equal: `(1,1,1,g)`, `(1,1,g,1)`, `(1,g,1,1)`, `(g,1,1,1)`;
  - two pairs: `(1,1,g,g)`, `(1,g,1,g)`, `(1,g,g,1)`.
- `++++--`, N-label normalized to `1`, P-labels:
  - `(1,1,g)`, `(g,1,1)`, `(1,g,g)`, `(g,g,1)`, `(g,1,g)`, `(g,g,g)`.

Claim: every word in these shapes injects its coefficient group.

These are the words with at least two same-sign coincidences not covered by
`kl-even-syllable-words-reduce-to-shorter-equations` (shapes `(1,1,1)` and
`(1,g,1)`) or by `kl-sign-index-two-infinite-order-loops-inject`.

**Why it matters.** With the other length-six fences, a length-six
Kervaire--Laudenbach violation over any group lies in this residue, or is one
of the one-coincidence or four-sign-change exceptions. A violation over
`L_(F_2)(1,2)^x` would also prove that group non-hyperlinear
(`kervaire-laudenbach-holds-for-hyperlinear`) and non-MF
(`kervaire-laudenbach-holds-for-mf`).

## Attempts

- **Relative weight test.** Impossible when both loops are involutions:
  - (WT2) on `y^2` and `x^2` forces weight one on both loops;
  - each trivial same-sign 2-cycle needs total weight two on its edges;
  - at least two coincidences leave at least three heavy corners, or two
    disjoint pairs, costing at least three;
  - the total exceeds the budget `n - 2 = 4`.
- **Substitution `z = t^2`.** Works only when every `t`-syllable exponent is
  even. `+++++-` always has a syllable `t^(-1)`. `++++--` is even exactly for
  `(1,1,1)` and `(1,g,1)`. Everything else here is odd.
- **Levin.** Needs all exponents of one sign; not applicable.
- **Next attack, not run.** Curvature redistribution on pictures in the style
  of Edjvet--Howie and Evangelidou: positive curvature sits only on degree-two
  regions labelled `y^2`, `x^2` or a trivial same-sign 2-cycle, and must be
  pushed to neighbouring discs. Alternatively, the index-four core for
  `+++++-`, where `w` has `z`-length one with `z = t^4`.
- **Novelty.** Edjvet--Juhász, *Non-singular equations over groups* I and II,
  could not be read: the session web budget was exhausted. Ivanov--Klyachko's
  length-six theorem assumes torsion-free coefficients and does not apply.
