---
rg: 2
id: labbe-wang-shift-has-polynomial-pattern-complexity-proof
kind: route
title: Letter images have shape at most (2,2), iterates double every 8 steps by primitivity, and every n×n pattern sits in the image of a legal 2×2 word
target: labbe-wang-shift-has-polynomial-pattern-complexity
requires: [labbe-substitution-is-primitive-and-recognizable]
artifacts:
  - research/artifacts/un-labbe-ring-substitution-complexity-2026-09-13.md
---

Artifact §3. `ω = αβγ` is Labbé's morphism (`labbe-substitution-is-primitive-and-recognizable`).

1. **Shapes at most (2,2).**
   - `α` and `β` send letters to letters or dominoes, in directions `e_2` and `e_1` respectively.
   - `γ` is a letter bijection.
   - By the concatenation rule, `shape(ω(u)) <= (2,2)` for every letter `u`.
2. **Iterates.**
   - On a legal word of shape `(w,h)`, `ω` acts column by column and row by row. So `shape(ω(x)) <= (2w,2h)`, and
     `shape(ω^m(a)) <= (2^m,2^m)`.
   - Every letter occurs in `ω^7(a)` (primitivity, `M^7 > 0`), and some letter has a `(2,2)` image. So every
     `ω^8(a)` has shape `>= (2,2)`.
   - Then `shape(ω^8(x)) >= (2w,2h)` for legal `x`, and `shape(ω^(8j)(a)) >= (2^j,2^j)`.
3. **Cover and count.**
   - `L(Ω_U) = \overline{ω(L(Ω_U))}^{Fact}` (`cor:OmegaU-is-aperiodic` with `lem:existence-omega-representation`;
     artifact §1, items 8 and 9).
   - With `m = 8⌈log_2 n⌉`, every `n × n` legal pattern is a subword of `ω^m(u)` for one of the 50 legal `2×2` words
     `u` (the cover step).
   - Each `ω^m(u)` has at most `4^(m+1)` positions of an `n × n` window.
   - So `p(n) <= 50 · 4^(8⌈log_2 n⌉+1) <= 50 · 4^9 · n^16`.
