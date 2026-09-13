---
rg: 2
id: heisenberg-irrational-center-has-rank-one-sector-tuples
kind: claim
title: The integer Heisenberg group has rank-one sector tuples in every dimension for every central character, although exact sector representations need zeta^d = 1
---

**ESTABLISHED** (`heisenberg-rank-one-sector-tuples-proof`). A calibration for the bounded-rank rung
of the Deligne covers.

Let `H = <a, b, z | [a,b] z^(-1), [a,z], [b,z]>` be the integer Heisenberg group, with
`[x,y] = x y x^(-1) y^(-1)`. Fix `zeta` in `U(1)` and `d >= 1`. Put `A` = the cyclic shift
`e_j -> e_(j+1 mod d)` on `C^d`, `B = diag(zeta^(-j))_(j = 0..d-1)`, `Z = zeta I`.

1. **Rank-one defects.** `[A,Z] = [B,Z] = I`, and
   `[A,B] Z^(-1) - I = diag(zeta^(-d) - 1, 0, ..., 0)` has rank at most one.
2. **Exact sector representations are rare.** A homomorphism `H -> GL_d(C)` with `z -> zeta I`
   exists iff `zeta^d = 1`: taking determinants in `[A,B] = zeta I` gives `zeta^d = 1`, and when
   `zeta^d = 1` the tuple above is exact.

**Consequences.**
- For `zeta` not a root of unity, `H` has unitary sector tuples with relator defects of rank at most
  one in **every** dimension, and no finite-dimensional sector representation at all. So the
  bounded-rank rung (`deligne-cover-bounded-rank-sector-tuples-have-bounded-dimension`) is false for
  `H` in the strongest form, with `k = 1`.
- For `zeta` of order `m >= 2` and `m` not dividing `d`, the rank-one tuple is within no rank of a
  genuine sector representation of the same dimension, since none exists. So the same-dimension
  rank-stability principle fails for this residually finite, linear, amenable group.
- The mechanism is a truncation: `A, B` compress the Schrodinger-type representation of `H` on
  `l^2(Z)` to an interval, and an interval of `Z` has boundary two, independent of its length.
  The operator-norm size of the defect, `|zeta^(-d) - 1|`, can be as large as `2`: the curvature
  is concentrated on one coordinate instead of being spread.
- Any proof of the rung for a group must therefore use an input that fails for `H`. For the
  Deligne covers the natural one is property (T), which excludes bounded-boundary truncations of
  genuine unitary sector representations
  (`kazhdan-reps-without-fd-subreps-have-linear-subspace-boundary`).
