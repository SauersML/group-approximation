---
rg: 2
id: heisenberg-rank-one-sector-tuples-proof
kind: route
title: Twisted cyclic shift and phase diagonal give rank-one Heisenberg sector defects
target: heisenberg-irrational-center-has-rank-one-sector-tuples
requires: []
---

Notation of the target. Indices are taken modulo `d`.

**Step 1: the commutator.** `A^(-1) e_j = e_(j-1)`, so `A B A^(-1) e_j = zeta^(-(j-1)) e_j` for
`1 <= j <= d-1`, and `A B A^(-1) e_0 = zeta^(-(d-1)) e_0` (the index `j - 1 = -1` is `d - 1`).
Hence `A B A^(-1) B^(-1)` is diagonal with entries

```text
zeta^(-(j-1) + j) = zeta          (1 <= j <= d-1),
zeta^(-(d-1))     = zeta^(1-d)    (j = 0).
```

So `[A,B] Z^(-1) = diag(zeta^(-d), 1, ..., 1)` and `[A,B] Z^(-1) - I` has rank at most one, with
equality to `0` iff `zeta^d = 1`. The relators `[a,z]` and `[b,z]` are exact because `Z` is scalar.

**Step 2: unitarity.** `A` is a permutation matrix and `B`, `Z` are diagonal with unimodular
entries, so the tuple is unitary.

**Step 3: exact sector representations.** If `phi : H -> GL_d(C)` has `phi(z) = zeta I`, then
`phi(a) phi(b) phi(a)^(-1) phi(b)^(-1) = zeta I`. The left side has determinant `1`, the right side
`zeta^d`. So `zeta^d = 1`. Conversely, when `zeta^d = 1`, Step 1 shows the tuple is exact.

**Step 4: the consequences.**
- If `zeta` is not a root of unity, Step 3 excludes exact sector representations in every
  dimension, while Steps 1-2 give unitary tuples with rank-one defects in every dimension. So no
  bound `d <= D(1)` holds.
- If `zeta` has order `m >= 2` and `m` does not divide `d`, Step 3 excludes a genuine sector
  representation of dimension `d`, so the same-dimension principle "within rank `C(k)` of a
  genuine representation" has no genuine representation to compare with.
- **Truncation picture.** On `l^2(Z)` put `(a f)(j) = f(j-1)`, `(b f)(j) = zeta^(-j) f(j)`,
  `z = zeta`. This is an exact representation, and on the interval `{0, ..., d-1}` the tuple of
  the target agrees with it except on the single coordinate where the shift wraps around. Intervals
  of `Z` have boundary two for every length. ∎
