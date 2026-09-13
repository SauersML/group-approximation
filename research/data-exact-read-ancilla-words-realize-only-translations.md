---
rg: 2
id: data-exact-read-ancilla-words-realize-only-translations
kind: claim
title: A word of track shears that reads the data track only while the data is exact, and realizes an automaton times the identity on ancilla tracks, realizes only a translation, so it cannot realize the integer marker
distinct_from:
  linearly-dirty-ancilla-words-realize-only-affine-data-maps: that allows linear reads of dirty data but only ancilla-independent nonlinear read values; this allows arbitrary nonlinear ancilla-dependent reads but no read of dirty data, so the classes are incomparable.
  one-ancilla-marker-residue-is-supported-on-window-overlaps: that computes the residue of one Bennett word and poses the integer decision; this rules out every word that never reads dirty data, the class the Bennett gate A' leaves.
  injective-binary-automata-are-stably-formalizable: that is the open hub; this blocks one construction class for its integer test object and invalidates no route.
artifacts:
  - research/artifacts/marker-nonlinear-ancilla-words-2026-09-12.md
---

**OPEN, pending verification by w7-vf-nonlinear** (w7-marker-nonlinear; proof in artifact Section 3).

**Setup.** Use Boolean points of `({0,1}^Z)^(1+k)`, with data track `d`, ancilla tracks `a` and initial
state `(x, y)`. The gates are track shears `s_T <- s_T + G(s_i : i != T)`, which are `Z`-equivariant
with finite memory. They include sitewise-linear maps, sitewise permutations and constant
translations.

**Statement.** Let `W` be a finite word of such gates with `W(x, y) = (F(x), y)` for all Boolean
`x, y`. Suppose every gate that reads the data track acts at a time when `d` depends only on `x`.
Then `F(x) = x + c`, where `c` is `0^Z` or `1^Z`. In particular `tau x id` is not such a word, for
any `k`.

**Proof idea.**
- For fixed `x`, the ancilla state is a bijection of `y` at every time.
- So a data write that keeps the data exact has a constant value.
- Over each maximal dirty interval, the net change of the data is a fixed map of the ancilla state at
  the start of the interval. Its value depends only on `x`, and the ancilla state runs over every
  configuration, so the net change is constant.

**Consequence.** With the linear-dirt theorem, a realization of `tau x id` needs a gate that reads
dirty data, and a nonlinear gate whose read value depends on `y` (artifact Corollary 3.2).
