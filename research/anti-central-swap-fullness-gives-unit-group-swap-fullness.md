---
rg: 2
id: anti-central-swap-fullness-gives-unit-group-swap-fullness
kind: route
title: Glue an anti-central corner solution to the projective witnesses it produces to invert the swap idempotent of the ternary unit group
target: ternary-leavitt-swap-idempotent-is-full
requires:
  - ternary-anti-invariant-swap-corner-is-full
  - ternary-leavitt-swap-problem-splits-at-central-involution
artifacts:
  - research/artifacts/anti-central-swap-fullness-gives-projective-2026-09-16.md
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

## Why sufficient

Corollaries 6.1 and 6.2 of the 2026-09-16 artifact. Let `c_- e_- b_- = eps_-` in `S_-`.

1. **Projective witnesses.** Theorem 5 of the artifact, the argument of
   `anti-central-swap-fullness-gives-projective-fullness`, builds `b, c` in `F_3[PG]` with `c ebar b = 1`
   directly from `b_-, c_-`.
2. **Gluing.** Part 1 of `ternary-leavitt-swap-problem-splits-at-central-involution` gives the unital
   isomorphism `theta : F_3[PG] -> S_+`, `[gbar] -> eps_+ [g]`, and the product decomposition `S = S_+ x S_-`.
   With it, `e = theta(ebar) + e_-`.
3. **Witnesses.** Put `B = theta(b) + b_-` and `C = theta(c) + c_-`. Products between the two central
   summands vanish, so

       C e B = theta(c ebar b) + c_- e_- b_- = eps_+ + eps_- = 1.

So the anti-central half alone gives the unit-group equation. This route and
`ternary-swap-fullness-projects-to-anti-invariant-half` form an intended two-route cycle: the two claims are
equivalent, and neither route establishes either claim alone.

It sharpens part 6 of the splitting claim. There, either half was shown to suffice for nonsurjunctivity. Here
the Leavitt-visible half is shown to imply the Leavitt-invisible half, and with it the full corner equation.
