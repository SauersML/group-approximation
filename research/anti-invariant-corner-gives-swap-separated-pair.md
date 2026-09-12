---
rg: 2
id: anti-invariant-corner-gives-swap-separated-pair
kind: route
title: Symmetrize a corner solution with the sign unit d to separate the swap
target: ternary-twisted-algebra-has-swap-separated-one-sided-pair
requires:
  - ternary-anti-invariant-swap-corner-is-full
  - ternary-leavitt-swap-problem-splits-at-central-involution
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/ternary-swap-separated-pairs-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

## Why sufficient

Let `c e_- b = eps_-` in `S_-`.

* `ternary-leavitt-swap-problem-splits-at-central-involution` supplies:
  * the relations `d^2 = 1` and `d w d = z w`;
  * the conjugation `[d] e_- [d] = eps_- - e_-`;
  * `[z] = -1` on `S_-`.
* **Setup.** Put `b' = e_- b` and `c'' = c e_-`, so that `c'' b' = eps_-`. Put
  `a = 2(b' + [d] b')` and `chat = c'' + c''[d]`.
* **Vanishing cross terms.** `c''[d] b' = c'' e_- [d] e_- b' = 0`, because
  `e_- [d] = [d](eps_- - e_-)`. So `chat a = 4 eps_- = eps_-`.
* **Separation.** From `w d = d z w` and `[w] b' = b'` we get `[w] a = 2(b' - [d] b')`. Hence
  `chat [w] a = 4(c'' b' - c'' b') = 0`.

This is the reverse half of an equivalence with `swap-separated-pair-gives-anti-invariant-corner`.
Theorem 1 of the artifact.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 27 of the verification artifact).
The sign `[w][d]b' = -[d]b'` uses `[z] = -1` on `S_-`. This is where the argument fails on `S_+`.

*Verified independently by `gk-vf-linear` (2026-09-12). Re-derived: `d w d = z w`, `[d] e_- [d] = eps_-(2 + [w]) = eps_- - e_-`, the vanishing cross terms `c e_- [d] e_- b = 0`, and the sign flip `[w][d] b' = -[d] b'` on `S_-`. See Section 1 of the linear-family verification artifact.*
