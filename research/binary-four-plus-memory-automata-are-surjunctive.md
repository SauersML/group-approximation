---
rg: 2
id: binary-four-plus-memory-automata-are-surjunctive
kind: claim
title: Over every group, an injective binary automaton with no memory of at most three elements is surjective
distinct_from:
  every-group-is-binary-surjunctive: that covers every binary automaton; this leaves out automata with a memory of at most three elements, a case that binary-three-address-strict-automata-are-linear reduces to f2-support-three-one-sided-units-are-units.
  binary-four-address-injective-automata-have-balanced-rules: that asks only for a balanced rule, and only at exactly four memory elements; this asks for surjectivity at every memory size from four on.
  binary-strict-pairs-need-a-memory-with-four-elements: that excludes strictness when encoder and decoder memories both have at most three elements; this asks for surjectivity when every encoder memory has at least four elements, with no condition on the decoder.
---

**OPEN.** Let `G` be a group and `tau : {0,1}^G -> {0,1}^G` an injective cellular automaton that
admits no memory set with at most three elements. Then `tau` is surjective.

Together with `binary-three-address-strict-automata-are-linear` and
`f2-support-three-one-sided-units-are-units`, this gives `every-group-is-binary-surjunctive`
(route `binary-surjunctivity-split-by-memory-size`).

## Attempts

- **Methods of the three-element case (2026-09-16, swarm-every-group-is-binary-surjunct).** These
  are the tests of `binary-three-address-strict-automata-are-linear` (artifact
  `research/artifacts/binary-three-address-strict-automata-linear-2026-09-16.md`, Section 8).
  - The single flip on a constant background (Lemma 3.1) extends verbatim. It kills every rule that
    is blind to single flips on a constant background.
  - The coset background (Lemma 4.1) needs the pattern to be decided by membership `h in U`. With two
    addresses outside the coset, the joint membership varies with `h`, so failure of the test no
    longer makes the memory group cyclic.
  - The selector flip system (Lemma 5.1) becomes a larger system over `F_2`, possibly with
    non-linear blindness conditions. It was not analyzed.
  - Where it dies: no case analysis of the rules at four addresses was attempted.
- **Balance at four elements is open.** The first step of the three-element reduction was balance.
  At four elements it is `binary-four-address-injective-automata-have-balanced-rules`, still OPEN.
  By that node's Attempts, a single-flip census leaves 195 unbalanced rule classes.
- **Linear rules contain direct finiteness over `F_2`.**
  - For `gamma in F_2[G]` with support `S`, put `L(x)(h) = sum_(s in S) x(h s)`.
  - The proof of Proposition 6.2 in the artifact above uses `|S| = 3` only in its notation. So `L` is
    injective and not surjective iff `gamma` has a left inverse and is not a unit.
  - Every memory of `L` contains `S`. If `s in S` is outside a memory `M'`, then `delta_s` agrees
    with `0` on `M'`, but `L(delta_s)(1) = 1 != 0 = L(0)(1)`.
  - Hence, when `|S| >= 4`, this claim implies that `gamma` is a unit whenever it has a left inverse.
  - The anti-involution `g -> g^-1` handles right inverses in the same way.
  - Where it dies: this is Kaplansky's direct finiteness over `F_2` for supports of at least four
    elements, open in general. `dykema-heister-juschenko-bounded-rank-direct-finiteness` covers
    only bounded support pairs.
