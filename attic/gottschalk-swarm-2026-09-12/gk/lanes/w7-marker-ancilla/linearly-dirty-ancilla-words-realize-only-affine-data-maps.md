---
rg: 2
id: linearly-dirty-ancilla-words-realize-only-affine-data-maps
kind: claim
title: A word of linear track moves and exact reads that realizes an automaton times the identity on ancilla tracks has an affine data map, so it cannot realize the integer marker
distinct_from:
  formalizable-binary-pairs-over-biorderable-groups-are-affine: that is one-track rigidity for formal pairs; this is multi-track rigidity for words of track moves with any number of ancilla tracks, restricted to reads whose values do not depend on the ancilla contents.
  one-ancilla-marker-residue-is-supported-on-window-overlaps: that computes the residue of one Bennett word and poses the integer decision; this rules out every word whose nonlinear gates read ancilla-independent values, the class that word leaves at its third gate.
  injective-binary-automata-are-stably-formalizable: that is the open hub; this blocks one construction class for its integer test object and invalidates no route.
artifacts:
  - research/artifacts/marker-ancilla-linear-dirt-invariant-2026-09-12.md
---

**ESTABLISHED** (w7-marker-ancilla; re-derivation requested from w3-vf-nonlinear). Work on the Boolean
points of `({0,1}^Z)^(1+k)`, with data track `s_1`, ancilla tracks `s_2, ..., s_(1+k)`, base point
`e = (x, y)` and `R = F_2[sigma^(±1)]`.

**Statement.** Let `W` be a finite word of moves of two kinds:
- *linear moves* `s <- E s` with `E in GL_(1+k)(R)` (linear track shears, partial shifts,
  sitewise-linear maps), and constant translations;
- *exact reads*: track shears `s_T <- s_T + G(s_i : i != T)`, with `G` `Z`-equivariant and of finite
  memory, whose read value at that point of the word depends only on `x`, for all Boolean `x, y`.

If `W(x, y) = (F(x), y)` for all Boolean `x, y`, then `F` is affine. In particular the marker
involution `tau x id` is not such a word, for any `k`.

**Invariant.** Every intermediate state is `M e + eta(x)`, with `M in GL_(1+k)(R)` and `eta` a
finite-memory map of `x`. Let `c` be the row with `c M = e_1^T`. The map `Q = c eta` is affine in `x`
at the start, and it stays affine along the word:
- linear moves leave `Q` unchanged;
- exact reads change it by a constant. A nonzero `c_T` makes the minor of `M` without row `T` and
  column `1` nonsingular. So for fixed `x` the other tracks run over every configuration, and `G` is
  constant.

At a realization, `Q = a^(-1) F - x` with `a` a monomial, so `F` is affine.

**Outside the class.**
- The Bennett word `A' B A` leaves the class at `A'`, which reads `m(x + y + m(x))`.
- The `4Z` word has four data tracks, and there the surjectivity step fails.
