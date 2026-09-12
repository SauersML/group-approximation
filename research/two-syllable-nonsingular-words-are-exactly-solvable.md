---
rg: 2
id: two-syllable-nonsingular-words-are-exactly-solvable
kind: claim
title: The two-syllable word c0 t c1 t c2 is exactly solvable, and the equal-exponent two-syllable word reduces to power words
artifacts:
  - research/artifacts/rgr-p-cyclic-twist-reduction-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `two-syllable-nonsingular-words-proof`; verification requested from
`w4-vf-linear-b`.

**Statement.** For `c_0, c_1, c_2 in GL_d(Fbar)` and any `lambda != 0`, there is `t in GL_(2d)(Fbar)`
with `c_0 t c_1 t c_2 = lambda 1_(2d)` exactly. Explicitly, with `K = c_0^(-1) lambda c_2^(-1)`, the
twisted `2`-cycle `t = [[0, K], [c_1^(-1), 0]]` on `Fbar^d (+) Fbar^d` works.

**Equal exponents.** `c_0 t^(e') c_1 t^(e') c_2` reduces to power words: `u = t^(e')` must satisfy
`u c_1 u = K`, i.e. `(c_1 u)^2 = c_1 K`; a square root over `Fbar` (established power case, amplifying for
the `p = 2` unipotent blocks) gives `u`, then `t = u^(1/e')` is another power word.

## Attempts

- **Unequal exponents `e_1 != e_2`.** `c_0 t^(e_1) c_1 t^(e_2) c_2` gives `t^(e_1) c_1 t^(e_2) = K`,
  mixing two different powers of the same `t` with an interposed coefficient. This is the smallest word
  not covered, and is open; it is one instance of the cyclic system of
  `rgr-p-reduces-to-cyclic-twist-system` with `e = e_1 + e_2` blocks.
- **General all-exponent-one `c_0 t c_1 ... t c_l`, `l >= 3`.** The `l = 2` commuting construction
  (`A B = B A = c_1 K`) does not obviously extend; open.
