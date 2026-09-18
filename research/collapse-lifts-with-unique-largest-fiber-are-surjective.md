---
rg: 2
id: collapse-lifts-with-unique-largest-fiber-are-surjective
kind: claim
title: A letter-collapse lift of an injective automaton with a unique largest fiber is surjective unless that fiber size is already a failing size
distinct_from:
  translating-transport-split-lifts-are-surjective: that kills one-letter split lifts whose rest map is a relabelled translation; this kills every letter-collapse lift with a unique largest fiber, whatever the rest map does, by replacing the translation with invariance of the uniform Bernoulli measure under the bijective rest map.
  passive-fixing-injective-automata-are-surjective: that assumes reserved symbols stay in place sitewise; this lets the lift rewrite every coordinate, requiring only that it commute with a letter collapse onto an injective automaton.
  reversible-automata-that-never-lower-rest-counts-preserve-them: that controls star designs whose star set moves by a reversible automaton with no data on the stars; this allows arbitrary data in every fiber and arbitrary injective dynamics of the collapsed configuration.
  nonsurjunctive-alphabet-sizes-are-upward-closed: that asks for strict automata at every larger size; this shows the letter-collapse lifts cannot supply the step k -> k+1 over a group with 2 not in NS(G).
  surjunctivity-failure-descends-to-binary-alphabet: that asks for descent to two symbols in general; this gives descent from n to n-1 only for strict automata with an autonomously evolving letter.
---

**ESTABLISHED** by `collapse-lift-bernoulli-window-count-proof`, from `bijective-ca-preserve-uniform-bernoulli-measure`
and `finite-injective-charge-noncreation-forces-surjectivity`. Notation `NS(G)` as in
`ec-groups-share-the-nonsurjunctive-alphabet-sizes`.

**Theorem.** Let `G` be any group, `A` and `B` finite alphabets, `r : B -> A` a surjection with fibers
`Q_a = r^{-1}(a)`, `τ` an injective cellular automaton on `A^G` and `Φ` an injective cellular automaton on `B^G` with

    r ∘ Φ = τ ∘ r.

Suppose some `a0 ∈ A` has `|Q_{a0}| >= 2` and `|Q_{a0}| > |Q_a|` for every `a != a0`. Then one of the following holds:
- `|Q_{a0}| ∈ NS(G)`;
- `τ` and `Φ` are both surjective.

The proof also gives, in the second case, `τ(a0^G) = a0^G` and the conservation law
`W(τ u) = W(u)` for every `u` with finitely many sites outside `a0`, where `W(u) = Σ_g log(|Q_{a0}| / |Q_{u(g)}|)`.

**Consequences.**
- **Ascent by one symbol through a collapse needs the binary witness.** Let `|B| = |A| + 1`. Every surjection
  `B -> A` has one fiber of size `2` and all others of size `1`, so the largest fiber is unique. If `2 ∉ NS(G)`, no
  strict automaton on `k + 1` symbols commutes with a letter collapse onto an injective automaton on `k` symbols,
  whatever the memories. This covers all one-letter split lifts, with any rest map, not only translations.
- **General ascent sizes.** A strict lift from `k` to `n` symbols through a collapse with a unique largest fiber of
  size `m` exists only if `m ∈ NS(G)`. The undecided collapse designs have at least two fibers of the largest size
  (the product lifts `τ × id`, which give the multiples, are of this kind), or do not commute with any collapse onto
  an injective automaton.
- **Descent from an autonomous letter.** Let `Φ` be strict on `n >= 3` symbols, and let `b` be a symbol whose
  occurrence set evolves autonomously: `Φ(y)^{-1}(b)` depends only on `y^{-1}(b)`, through an injective binary
  automaton. Collapse the other `n - 1` symbols to one letter. The largest fiber is unique of size `n - 1`, and `Φ`
  is not surjective, so `n - 1 ∈ NS(G)`.
- **What was new.** The count of `translating-transport-split-lifts-are-surjective` needed a rigid translation far
  from the defect. Here the rest map is an arbitrary injective automaton. If it is not surjective, its fiber size
  already fails; if it is bijective, invariance of the uniform measure does the counting exactly.
