---
rg: 2
id: kl-length-six-residue-power-words-proof
kind: route
title: Multiply out the inner words, then substitute them into the root equations z^2 c and z^4 c
target: kl-length-six-residue-squares-and-fourth-powers-inject
requires:
  - kl-substituting-a-short-inner-word-preserves-injectivity
  - kl-length-at-most-five-equations-are-solvable
---

**Identities.** Each is free cancellation of `t^(-1) t` in `G * <t>`.
- (S1) `u^2 = t a_1 t a_2 t y t^(-1) t a_1 t a_2 t y t^(-1) = t a_1 t a_2 t (y a_1) t a_2 t y t^(-1)`,
  so `u^2 x = w` when `a_3 = y a_1` and `a_4 = a_2`.
- (S2) `u^2 = t^(-1) x t a_1 t a_4 t t^(-1) x t a_1 t a_4 t = t^(-1) x t a_1 t (a_4 x) t a_1 t a_4 t`,
  so `u^2 y = (t^(-1) x) w (t^(-1) x)^(-1)` when `a_2 = a_4 x` and `a_3 = a_1`.
- (S3) By induction on `k`, `u^k = t a_1 (t (y a_1))^(k-1) t y t^(-1)`: the step is
  `u^k u = t a_1 (t (y a_1))^(k-1) t y a_1 t y t^(-1)`. So `u^4 x = w` when
  `a_2 = a_3 = a_4 = y a_1`.
- (S4) By the same induction, `u^k = t^(-1) x (t (a_4 x))^(k-1) t a_4 t`. So
  `u^4 y = (t^(-1) x) w (t^(-1) x)^(-1)` when `a_1 = a_2 = a_3 = a_4 x`.

Conjugate words have the same normal closure, so it suffices to treat `u^2 c`
and `u^4 c` with `c in {x, y}`.

**Outer equations.** Put `v = z^k c` with `k in {2, 4}` and `c in G`. It has
variable length `k <= 5` and degree `k != 0`. By
`kl-length-at-most-five-equations-are-solvable`, `G -> (G * <z>)/<<v>>` is
injective. Directly, this quotient is the amalgam of `G` with a cyclic group
along `z^k = c^(-1)`.

**Inner words.** In (S1) and (S2), `u` has variable length four and degree two.
In (S3) and (S4), it has variable length three and degree one. Each case has
`w = sigma_u(v)` up to conjugation, so
`kl-substituting-a-short-inner-word-preserves-injectivity` gives injectivity.

**Residue sub-cases.** The normalizing shift `t -> s c^(-1)` of
`kl-even-syllable-reduction-proof` sends `a_i -> c^(-1) a_i` and
`y -> c^(-1) y c`, and fixes `x`. It preserves each hypothesis, since
`c^(-1) a_3 = (c^(-1) y c)(c^(-1) a_1)` iff `a_3 = y a_1`, and
`c^(-1) a_2 = (c^(-1) a_4) x` iff `a_2 = a_4 x`. So the conditions may be tested
on normalized labels. Checking the eight normalized `+++++-` shapes:

| Shape | (S1) | (S2) | (S3) | (S4) |
|---|---|---|---|---|
| `(1,1,1,1)` | needs `y = 1` | needs `x = 1` | needs `y = 1` | needs `x = 1` |
| `(1,1,1,g)` | `a_4 != a_2` | `g = x^(-1)` | labels unequal | `g = x^(-1)` |
| `(1,1,g,1)` | `g = y` | `a_3 != a_1` | labels unequal | labels unequal |
| `(1,g,1,1)` | `a_4 != a_2` | `g = x` | labels unequal | labels unequal |
| `(g,1,1,1)` | `g = y^(-1)` | `a_3 != a_1` | `g = y^(-1)` | labels unequal |
| `(1,1,g,g)` | `a_4 != a_2` | `a_3 != a_1` | labels unequal | labels unequal |
| `(1,g,1,g)` | needs `y = 1` | needs `x = 1` | labels unequal | labels unequal |
| `(1,g,g,1)` | `a_4 != a_2` | `a_3 != a_1` | labels unequal | labels unequal |

Loop coefficients of cyclically reduced words are nontrivial, so the cells
"needs `y = 1`" and "needs `x = 1`" never hold.
