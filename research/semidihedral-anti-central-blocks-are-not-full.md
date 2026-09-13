---
rg: 2
id: semidihedral-anti-central-blocks-are-not-full
kind: claim
title: The transpose-twisted evaluation kills the evaluation block, so neither semidihedral block of the ternary anti-central summand is full
distinct_from:
  ternary-anti-central-pairs-visible-or-invisible: that normalizes one-sided pairs through the evaluation alone; this adds the transpose-twisted evaluation, which together with the evaluation maps the summand onto R x R and kills one semidihedral block each.
  ternary-anti-invariant-swap-corner-is-full: that asks whether the swap idempotent is full; this proves the two semidihedral block idempotents are not, through two quotients that agree on the signed Thompson group and so cannot see the swap idempotent.
artifacts:
  - research/artifacts/semidihedral-and-gl2-f3-blocks-forced-states-2026-09-12.md
---

**ESTABLISHED** (proof: route `semidihedral-blocks-not-full-proof`; verified by `w4-vf-linear-b`, Section 40 of
`research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`).

Let `R = L_(F_3)(1,2)`, `G = R^x`, `S_- = eps_- F_3[G]`, `pi : S_- -> R` the evaluation, `alpha(g) = (g^*)^(-1)`, and
`pi' = pi o alpha_*`. Let `SD = <w, d, h>`, `c_2 = -eps_-(1 + [wh] + [dh])` and `c_1 = eps_- - c_2`.

1. `pi(c_1) = 1`, `pi(c_2) = 0`, `pi'(c_1) = 0` and `pi'(c_2) = 1`, and `(pi, pi') : S_- -> R x R` is onto.
2. An idempotent matrix `p` with `pi(p) = 0` or `pi'(p) = 0` generates a proper ideal. So no idempotent matrix over one
   block alone is full, and `eps_- S_- (+) X ~= (c_i S_-)^m` has no solution for any `m >= 1` and projective `X`.
3. `pi' = pi` on `F_3[H] eps_-` for the signed Thompson group `H`, so part 2 says nothing about idempotents over `H`.

Since `K_0(R) = 0`, the two quotients give no obstruction to stabilized relations.
