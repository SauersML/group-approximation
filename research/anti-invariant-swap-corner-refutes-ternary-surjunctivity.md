---
rg: 2
id: anti-invariant-swap-corner-refutes-ternary-surjunctivity
kind: route
title: A one-sided inverse on the anti-central summand is a direct-finiteness failure of the whole group algebra
target: ternary-leavitt-unit-group-nonsurjunctive
requires: [ternary-anti-invariant-swap-corner-is-full, ternary-leavitt-swap-problem-splits-at-central-involution, stable-finiteness-failure-refutes-surjunctivity]
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

From `c e_- b = eps_-` in `S_-`, put `A = e_- b + eps_+` and `C = c + eps_+`.
* The idempotents `eps_+` and `eps_-` are central and orthogonal, so `CA = eps_- + eps_+ = 1`.
* If `AC = 1`, then `e_- (b c) = eps_-`. An idempotent with a right inverse in the unital ring
  `S_-` equals its unit, so `e_- = eps_-`.
* That is false: `1, [w], [z], [zw]` are distinct basis elements of `F_3[G]`.

So `A` is one-sided invertible but not invertible in `F_3[G]`, and
`stable-finiteness-failure-refutes-surjunctivity` gives a strict linear automaton on the full shift
over `G`.

Section 23 of the verification artifact, and correction 7.4(e) of the ternary artifact.

*Second independent verification by `gk-vf-linear` (2026-09-12). `CA = 1` holds. `AC = 1` would force `e_- = eps_-`, but `eps_- - e_- = 2(1 + 2[w] - [z] - 2[zw])` is nonzero, because `1, w, z, zw` are distinct. So the direct-finiteness failure holds on the full shift `F_3^G`. See Section 2 of the linear-family verification artifact.*
