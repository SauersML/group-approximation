---
rg: 2
id: strict-automaton-upsets-give-smaller-nonsurjunctive-sizes
kind: claim
title: An injective automaton whose restriction to a sitewise absorbing sub-alphabet is onto is itself onto, so every proper upset of a strict automaton carries a strict automaton on fewer symbols over the same group
distinct_from:
  transition-digraph-capacity-lifts-give-nonsurjunctive-sizes: that lifts sizes up, putting capacity sums with every capacity at least 1 in NS(G), and proves only the size-1 case of this (item 4, no singleton upset); this descends, putting the size of every proper nonempty upset itself in NS(G), with the same group, memory and table.
  finite-injective-charge-noncreation-forces-surjectivity: that allows a single zero-charge symbol and says several zero-charge symbols "can carry arbitrary computation that this charge does not control"; this is exactly the several-symbol case, with the hypothesis that the zero-charge sub-shift is carried onto itself.
  passive-fixing-injective-automata-are-surjective: that needs every passive letter held in place; this lets letters outside the upset move freely and asks only that the restriction to the upset be onto.
  surjunctivity-failure-descends-to-binary-alphabet: that asks for descent all the way to two symbols with tables allowed to change; this gives a same-table descent that stops exactly at automata whose transition digraphs of all powers are strongly connected.
  collapse-lifts-with-tied-largest-fibers-are-surjective: that constrains lifts through letter collapses (ascent); this is restriction to a sub-alphabet (descent).
---

**ESTABLISHED** by `upset-restriction-pinned-particle-count`. Elementary, no imports.

**Setting.** As in `transition-digraph-capacity-lifts-give-nonsurjunctive-sizes`. `G` is any group, `A` a finite
alphabet, `τ(x)(g) = μ((g^(-1)x)|_M)` with `1 ∈ M` finite. `R(τ) = {(u(1), μ(u)) : u ∈ A^M}`. A set `U ⊆ A` is an
*upset* if `(a, b) ∈ R(τ)` and `a ∈ U` imply `b ∈ U`, i.e. `x(g) ∈ U` implies `τ(x)(g) ∈ U`. Then `τ(U^G) ⊆ U^G`,
and `τ_U = τ|_(U^G)` is the automaton over the alphabet `U` with table `μ|_(U^M)`.

**Theorem (upset descent).** Let `τ` be injective on `A^G` and `U` a nonempty upset of `R(τ)`. If `τ_U` is
surjective, then `τ` is surjective.

**Corollaries.** Let `τ` be strict on `A^G`, `|A| = k`.
1. For every nonempty proper upset `U`, `τ_U` is strict, so `|U| ∈ NS(G)` and `|U| < k`. The case `|U| = 1` is
   item 4 of the capacity-lift theorem (`τ_U` on one symbol is always onto).
2. **Powers.** `τ^p` is strict and `R(τ^p) ⊆ R(τ)^p` (relation composition). So every nonempty proper
   `U ⊆ A` closed under `R(τ)^p` for some `p >= 1` has `|U| ∈ NS(G)`. Examples: every sink class of `R(τ)`; every
   cyclic class of a sink class of period `d > 1` (closed under `R(τ)^d`).
3. **Normal form.** If `NS(G) ≠ ∅` and `n0 = min NS(G)`, every strict automaton on `n0` symbols has, for every
   `p >= 1`, `R(τ^p)` strongly connected. In particular `R(τ)` is strongly connected and aperiodic (primitive):
   a period `d > 1` would make each cyclic class a proper upset of `τ^d`. The same holds with `NS_all` and any
   group attaining `min NS_all`.
4. **At the minimal size capacity lifts are trivial.** For such `τ` every capacity is constant, since capacities
   are monotone along a strongly connected digraph. So item 1 of the capacity lift gives only multiples of `n0`,
   and `g(τ) = n0`.
5. **Singleton classes.** If `{c}` is a class (no cycle other than the loop passes through `c`), let `↑c` be the
   forward closure of `c`. Both `↑c` and `↑c \ {c}` are upsets: a return to `c` from `↑c \ {c}` would close a
   cycle through `c`. `↑c = {c}` is excluded by corollary 1. So `|↑c| - 1` and `|↑c|` both lie in `NS(G)` (the
   second possibly as `k`). No additive closure of `NS(G)` is known, so this does not by itself give cofiniteness;
   that follows in this case from `g(τ) = 1` and capacity-lift item 3.

**Why it matters.**
- It is the first **descent** of strictness to fewer symbols over the same group, with no change of memory or
  table. Every recorded descent attempt on `surjunctivity-failure-descends-to-binary-alphabet` changes tables or
  groups, and `equal-label-table-is-strict-at-three-symbols-not-two` shows fixed table families need not descend.
  This shows fixed *automata* descend along every proper upset.
- *Where it stops.* Upset descent ends at automata all of whose powers have strongly connected transition
  digraphs, and by corollary 3 every strict automaton at the minimal failing size is of that kind. So upset
  descent can reach two symbols over `G` only when `min NS(G) = 2`, and at `min NS(G) > 2` it is stuck at
  primitive digraphs. A proof by restriction to
  sub-alphabets must therefore use sets that are closed under `τ` on configurations but not sitewise. For those the
  theorem gives nothing: `τ` permutes the constants, so every singleton `{a}` with `σ(a) = a` has `τ(a^G) = a^G`,
  and `τ_{a}` is onto while `τ` is strict.
- *Binary powers.* Capacity lifts from a minimal-size strict automaton certify only `n0 Z`. The capacity-lift class
  can produce a power of two only from a strict automaton at a non-minimal size whose transition digraph (or that
  of a power) is not strongly connected, or when `n0` is already a power of two.
