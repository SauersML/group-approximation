---
rg: 2
id: leavitt-nielsen-collision-light-corners-proof
kind: route
title: Read the four same-sign labels of the collision word off its matrices and apply the four-corner theorem
target: leavitt-nielsen-collision-candidate-injects
requires:
  - kl-four-same-sign-corner-words-inject
---

**Hypotheses of the four-corner theorem.** `W_col = a t^2 a t p t e t^(-1) q t^(-1)`.
- `deg_t(W_col) = 2`, and its sign class is `++++--`.
- It is cyclically reduced: the coefficients between opposite letters are `e`
  (between `t` and `t^(-1)`) and `a` (between the last `t^(-1)` and the first
  `t`), both nontrivial.
- It is not a proper power. A square root would have `t`-length three and sign
  pattern `sigma`, with `sigma sigma` a rotation of `++++--`. The rotations are
  `++++--`, `+++--+`, `++--++`, `+--+++`, `--++++` and `-++++-`, and none
  repeats a length-three block. Higher powers do not divide length six with an
  integer degree.

**Corners.** Reading cyclically, and splitting `t^2`:

| Corner | Type | Label |
|---|---|---|
| `t . 1 . t` | P | `1` |
| `t . a . t` | P | `a` |
| `t . p . t` | P | `p` |
| `t . e . t^(-1)` | loop at `t^-` | `e` |
| `t^(-1) . q . t^(-1)` | N | `q` |
| `t^(-1) . a . t` | loop at `t^+` | `a` |

**Light corners.** A same-sign corner is heavy only if another corner of its
type has the same label, or a corner of the other type has the inverse label.
Compare the matrices in `GL_20(L)`, `L = L_(F_2)(1,2)`, entry by entry. Here
`L != 0`, and `E_ij` are matrix units.
- `a = I + s_0 E_12` is not `1`, since its `(1,2)` entry is `s_0`.
- `p` has zero diagonal, so `p != 1` and `p != a`.
- The two factors of `q` commute, since their index pairs are disjoint, so
  `q = I + s_1 E_34 + t_0 E_(11,12)`. This gives:
  - `q != 1`;
  - `q != a^(-1) = a`, because the `(3,4)` entries are `s_1` and `0`;
  - `q != p^(-1)`, because the diagonal of `q` is `1` and that of `p^(-1)` is `0`.

So the P-labels `1, a, p` are pairwise distinct, and no P-label is inverse to
the N-label `q`. All four same-sign corners are light, and `r = 4`.

**Conclusion.** Part 1 of `kl-four-same-sign-corner-words-inject` gives that
`G -> (G * <t>)/<<W_col>>` is injective and that every reduced spherical picture
is empty. That part places no torsion hypothesis on the loop coefficients.
