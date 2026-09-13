---
rg: 2
id: deligne-sector-truncations-have-bounded-dimension
kind: claim
title: Bounded-boundary truncations of unitary sector representations of a Deligne cover have dimension at most 2B / kappa^2
distinct_from:
  heisenberg-irrational-center-has-rank-one-sector-tuples: that shows truncation yields rank-one sector tuples of every dimension for the integer Heisenberg group; this shows property (T) caps the dimension of every truncation for the Deligne covers.
  deligne-monomial-twisted-modules-have-no-folner-truncations: that excludes coordinate Folner truncations of one infinite monomial module over finite fields; this excludes bounded-boundary truncations of every unitary sector representation, with a dimension bound from a Kazhdan constant.
---

**ESTABLISHED** (`deligne-sector-truncations-bounded-dimension-proof`). Unreviewed.

**Setting.** `g >= 2`, `n >= 3`, `Gamma_n` the preimage of `Sp_(2g)(Z)` in the connected `n`-fold
cover of `Sp_(2g)(R)`, `z` the covering generator, `<S cup {z} | R>` a finite presentation, and
`kappa_n > 0` a Kazhdan constant for `S cup {z}`. Fix `zeta` with `zeta^n = 1` and `zeta^2 != 1`.

**Theorem.**
1. Every unitary representation `pi` of `Gamma_n` with `pi(z) = zeta` has no nonzero
   finite-dimensional subrepresentation.
2. For every such `pi` and every finite-dimensional subspace `W`,
   `max_(s in S) (dim W - dim(W n pi(s) W)) >= kappa_n^2 dim W / 2`.
3. **Truncation bound.** Call a unitary tuple `rho : S cup {z} -> U(W)` with `rho(z) = zeta I` a
   **`B`-truncation of `pi`** if `W <= H` and every `s` in `S` has a subspace `W_s <= W` of
   codimension at most `B` with `rho(s) w = pi(s) w` for `w` in `W_s`. Then `dim W <= 2B / kappa_n^2`.
4. A `B`-truncation is a sector tuple whose relator defects have rank at most `|r| B`, where `|r|`
   is the length of `r`. So truncation is a mechanism for bounded-rank sector tuples, the one that
   works for the integer Heisenberg group, and for the Deligne covers it only produces bounded
   dimension.

**Scope.**
- **A firewall on constructions, not a proof of the rung.** The bounded-rank rung
  `deligne-cover-bounded-rank-sector-tuples-have-bounded-dimension` is *equivalent* to the
  statement that every rank-`k` sector tuple is a `C(k)`-truncation of some unitary sector
  representation. If the rung holds, embed `W` in any infinite-dimensional sector representation
  (for example the one induced from `<z>`) with `W_s = 0`. Conversely, item 3 turns a truncation
  constant into a dimension bound. So a countermodel must be far from every genuine sector
  representation in the truncation sense, with codimension unbounded in `k`.
- **Unitary only.** Over any field the non-unitary analogue of item 2 fails for Kazhdan groups
  (`kazhdan-rank-rounding-fails-over-every-field`). Whether `Gamma_n` has algebraic sector modules
  over `C` with bounded-boundary subspaces of unbounded dimension is not decided here.
