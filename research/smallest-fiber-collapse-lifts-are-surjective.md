---
rg: 2
id: smallest-fiber-collapse-lifts-are-surjective
kind: claim
title: A letter-collapse lift of a bijective automaton with a unique smallest fiber is surjective unless that fiber size is already a failing size
distinct_from:
  collapse-lifts-with-unique-largest-fiber-are-surjective: that uses the largest fiber as background, where the window count makes the base lose charge and surjectivity of the base comes out; this uses the smallest fiber, where the count reverses sign, so bijectivity of the base is assumed and charge noncreation is applied to its inverse.
  count-raising-reversible-automata-lower-biased-rokhlin-entropy: its autonomous star designs are the case s = 1 here (a star letter carrying no data); this allows s >= 2 data values at the background letter and any fiber profile above it.
  reversible-automata-that-never-lower-rest-counts-preserve-them: that is the unit-charge count statement behind the star designs; this needs the logarithmic fiber charge log(|Q_a|/s) and a Bernoulli window count at a background carrying data.
  nonsurjunctive-alphabet-sizes-are-upward-closed: that asks for strict automata at every larger size; this shows collapse designs over a bijective base must have at least two smallest fibers, unless the smallest fiber size already fails.
  surjunctivity-failure-descends-to-binary-alphabet: that asks for descent to two symbols in general; this gives descent to 2 or to the smaller part for strict automata whose sub-alphabet occurrence set evolves autonomously.
  passive-fixing-injective-automata-are-surjective: that fixes reserved symbols sitewise; this lets every coordinate be rewritten, requiring only a factor relation onto a bijective automaton.
---

**ESTABLISHED** by `smallest-fiber-collapse-dual-background-proof`, from `bijective-ca-preserve-uniform-bernoulli-measure`
and `finite-injective-charge-noncreation-forces-surjectivity`. Notation `NS(G)` as in
`ec-groups-share-the-nonsurjunctive-alphabet-sizes`.

**Theorem.** Let `G` be any group, `A` and `B` finite alphabets, `r : B -> A` a surjection with fibers
`Q_a = r^{-1}(a)`, `τ` a **bijective** cellular automaton on `A^G` and `Φ` an injective cellular automaton on `B^G`
with

    r ∘ Φ = τ ∘ r.

Suppose some `a0 ∈ A` has `s = |Q_{a0}| < |Q_a|` for every `a != a0`. Then one of the following holds:
- `s >= 2` and `s ∈ NS(G)`;
- `Φ` is surjective.

In the second case some power `τ^j` fixes `a0^G` and conserves `W'(u) = Σ_g log(|Q_{u(g)}| / s)` on configurations
with finitely many sites outside `a0`.

**Consequences.**
- **Both extremes.** Put this together with `collapse-lifts-with-unique-largest-fiber-are-surjective`. Let `Φ` be strict
  and commute with a collapse onto an injective `τ`. Then `τ` is strict (so `|A| ∈ NS(G)`), or `τ` is bijective and
  both of the following hold:
  - the largest fiber size lies in `NS(G)`, or at least two letters attain it;
  - the smallest fiber size lies in `NS(G)`, or at least two letters attain it.

  So a strict collapse design over a bijective base whose extreme fiber sizes do not already fail must have **two
  letters of the largest size and two letters of the smallest size**, or all fibers equal. For ascent from `k` to
  `n` symbols over a bijective base on `|A|` letters, this excludes every fiber profile with a unique extreme, such as
  `(3,2,2)` and `(2,2,1)`. The first profiles left undecided are `(2,2,1,1)` and the equal profiles `τ × id`.
- **Autonomous sub-alphabet.** Let `Φ` be strict on `n` symbols, and let `D ⊂ B` with `|D| = j`, `1 <= j < n/2`, such
  that the output occurrence set of `D` depends only on the input occurrence set of `D`, through an injective binary
  automaton `β`. Then:
  - `n - j ∈ NS(G)` (largest fiber);
  - if `β` is bijective, then `j >= 2` and `j ∈ NS(G)` (this theorem). Otherwise `β` is strict and `2 ∈ NS(G)`.

  So `n - j ∈ NS(G)`, and `2 ∈ NS(G)` or `j ∈ NS(G)`. For `j = 1` (one autonomous letter) this gives `2 ∈ NS(G)` and
  `n - 1 ∈ NS(G)`. That is the established star-design case, now with `n - 1` added.
- **Ascent through an autonomous region.** Over a group with `2 ∉ NS(G)`, a strict automaton on `k + j` symbols
  with `j < k` built by moving `j` extra letters as an autonomous injective region needs `j ∈ NS(G)` and
  `k ∈ NS(G)`. The ascent step itself (`j` small, not yet a failing size) is impossible in this form, whatever data
  the old `k` letters carry and however the region moves.

**What is new.** The largest-fiber count makes the base automaton lose fiber charge, so charge noncreation applies
to `τ` directly. At the smallest fiber the same window count gives the opposite inequality `W'(u) <= W'(τ u)`. That
inequality says nothing about `τ`, but it says `τ^{-1}` never creates charge. So bijectivity of the base replaces
injectivity, and the whole of Steps 0–3 and 5 of the largest-fiber proof carries over with the background at the
smallest fiber.

**Calibration.**
- `s = 1`, `A = {0,1}`: this is the autonomous star design of
  `count-raising-reversible-automata-lower-biased-rokhlin-entropy`, which is surjective once the star count is
  preserved, and that count is preserved by `reversible-automata-that-never-lower-rest-counts-preserve-them`.
- Product lifts `τ × id_P` have all fibers equal, so neither theorem applies. They are surjective anyway, since `τ`
  is bijective.

**Where it stops.** The designs left are:
- designs with two letters of each extreme size;
- factor maps that are block codes rather than letter collapses;
- a base `τ` that is only injective. Then `τ` is strict and only `|A| ∈ NS(G)` follows, which says nothing about
  ascent when `|A| < n`.
