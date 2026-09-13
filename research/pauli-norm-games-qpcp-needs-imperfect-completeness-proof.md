---
rg: 2
id: pauli-norm-games-qpcp-needs-imperfect-completeness-proof
kind: route
title: Translate test acceptance into Pauli frustration and apply stabilizer rounding
target: pauli-norm-games-qpcp-needs-imperfect-completeness
requires: [pauli-sums-near-their-one-norm-round-to-stabilizer-states, pauli-projector-hamiltonians-are-stabilizer-approximable, natarajan-vidick-games-pcp-amplification-error]
artifacts:
  - research/artifacts/pauli-frustration-stabilizer-rounding-2026-09-12.md
---

**(GT1).** Acceptance at least `1-eps` is equivalent to `tr(H rho) >= W(1-2eps)`,
that is, Pauli frustration at most `2W eps`. So YES instances have
`lambda_max >= W - 2W eps_c` and NO instances have `lambda_max <= W - 2W eps_s`.
With `F_Y = 2W eps_c` and `F_N = 2W eps_s`, the hypothesis is `F_N > (2+sqrt2)F_Y`.
That promise problem is in NP by the Pauli-sum clause of
`pauli-projector-hamiltonians-are-stabilizer-approximable`. If `eps_c = 0`, every
`sign(beta_P)P` has expectation one in some state, so all pairs commute and the
system is consistent. Both conditions are checked by `F_2` linear algebra.

**(GT2), NP side.** Let the decomposition have weight `W <= 1`. A YES instance has
`W - lambda_max <= 1 - (1-1/p) = 1/p`. By
`pauli-sums-near-their-one-norm-round-to-stabilizer-states`, some stabilizer state
has energy at least `lambda_max - (1+sqrt2)/p >= 1 - (2+sqrt2)/p`. Every state of a
NO instance has energy at most `1-1/q`. If `(2+sqrt2)/p < 1/q`, the verifier checks
a stabilizer tableau against a rational threshold in between.

**(GT2), the lemma's gap.** By the lemma (cited in
`natarajan-vidick-games-pcp-amplification-error`), `H'` has
`lambda_max >= 1-k/p` or `<= 2e^(-k/(2q)) - 1`, and weight at most `3` when the input
weight is at most one. The test on `H'` has acceptance gap
`(lambda_Y - lambda_N)/(2W') >= (2 - k/p - 2e^(-k/(2q)))/6`. With `x = k/(2q)` and
`r = p/q` this is `(1 - x/r - e^(-x))/3`. At `x = ln r` it equals
`(1-(1+ln r)/r)/3`, and `ln r < r-1` makes it positive for `r > 1`. Section 4 of the
linked artifact gives the numbers.
