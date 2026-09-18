---
rg: 2
id: absorbing-rope-readers-are-not-pointwise-rigid
kind: claim
title: A rope reader whose automaton merges two states (every automaton for a language that is not a group language, such as Cohen's digit set) hides the tail choice above a merging word, so sibling subtrees below it carry independent free choices and the reader is not pointwise rigid; readers with injective (group) automata link all tails, so rigid rope seeding needs rope index sets that are group languages
requires:
  - coupled-rope-reader-has-nested-one-bit-fibres
  - rope-readers-cannot-be-deterministic-and-must-couple-chains
  - extension-rigidity-is-base-centrality-plus-pointwise-rigidity
invalidates:
  - coupled-rope-reader-has-nested-one-bit-fibres
distinct_from:
  coupled-rope-reader-has-nested-one-bit-fibres: that claims every free chain is linked into one bit; this shows the claim fails whenever a merging word separates two sibling subtrees, which happens for Cohen's rope set.
  rope-readers-cannot-be-deterministic-and-must-couple-chains: that refutes deterministic readers and says co-determinism maximizes free runs; this shows injectivity is exactly what makes the free runs linkable.
---
**ESTABLISHED** for parts 1–3 (lane proof, bh-invent-15, 2026-09-18; not reviewed). Part 4 is a
sketch.
- **Correction.** Part 2 of `coupled-rope-reader-has-nested-one-bit-fibres` (every free chain
  linked into one bit) is **false** for Cohen's rope set. Its step "consecutive positions are
  linked" treats the common value `s = q(hl) = q(hxl)` as carrying the free choice. When a bad
  digit lies below the link level, `s` is forced to `bad`, and the link carries nothing.
- **Consequence for the coordinator's route.** The proposed route to (C_D) via tail events is
  moot: pointwise rigidity already fails (part 2). It also would not have been a proof as
  stated, because quantum families carry no measure. "`E` is tail-measurable" presupposes that
  `E` lies in the base algebra, which is (C_D) itself.
- **The rigorous substitute for tails.** Base marginals commute (the base is rigid), so they
  generate a Boolean algebra whose Stone space lies in `Y`. Clopen identities valid on `Y` then
  hold as operator identities.

## Setting
The scaling seed of `S_M` with a reader: states `Q`, and the upward rule
`q(h) = δ(q(hl), d(h))` with `q = q_0` at origins, on row sites of a region. Links (such as the
block links (L)) are local rules equating reader values at nearby sites. A **merging word** is a
digit word `u` and states `s ≠ s'` with `δ(s,u) = δ(s',u)`.

## Theorem
1. **Merges exist for non-group languages.** If `I` (as numerals read most-significant digit
   first) is not a group language, every deterministic automaton recognizing it has a merging
   word.
   - Cohen's `I` (digits in `{1,…,2n}`) is not a group language: `ok` merges into the absorbing
     `bad` on any bad digit.
   - More generally, no set that excludes all numerals containing a fixed forbidden digit is a
     group language.
2. **Merges hide the tail and split the fibre.** Suppose `u` merges `s, s'`, and both `s` and
   `s'` occur as tail states of free chains, as `ok`/`bad` do for Cohen's `I`. Then some boundary
   base configuration has two sibling subtrees whose free choices are independent under every
   link rule that reads only reader values at bounded distance. So the reader is not pointwise
   rigid, hence not quantum rigid, by `extension-rigidity-is-base-centrality-plus-pointwise-rigidity`
   (item 2).
3. **Injective automata link everything.** If every digit acts injectively on `Q` (a group
   automaton), then the reader value at any site determines its chain's tail state. So links
   transmit tails across any number of levels, and the linking argument of the parent goes
   through verbatim. Every fibre is then one global tail choice, a single partition of unity
   transported by permutations, and it is pointwise rigid.
4. **Consequence (sketch).** Rigid rope seeding by finite-state readers requires rope index sets
   that are group languages. By part 1, the Aanderaa–Cohen rope set is excluded.
   **New gate (GL):** find a Higman–Clapham-type tower whose infinitely generated associated
   subgroups are indexed by group languages, or by residue-periodic sets, which have
   deterministic readers. Equivalently, find a modular machine that tolerates the extra rope
   letters a group language admits.

## Proof
**1.** A deterministic automaton recognizes a group language iff its transition monoid is a
group (standard), that is, iff every letter acts as a permutation. If some letter acts
non-injectively, it merges two states.
- For the claim about forbidden digits: a group language is closed under inserting `w^N`, with
  `N` the exponent of the group. So inserting a block of forbidden digits cannot exclude a word.

**2.**
- **The configuration.** Choose `α_N` whose numeral is `(tail block)·u·a`, where:
  - the tail block admits both left-infinite runs, ending in `s` and in `s'`; for Cohen's `I`,
    all digits good;
  - `u` is the merging word, placed at levels `1..|u|`;
  - `a` is a digit, with `a` and `a+1` both at most `m − 2`.

  Take a limit of `g_N·y_*^+` centred on the row positions `α_N` and `α_N + 1` of one coset `C`.
- **Where the subtrees sit.** In the limit their `l`-images at level 1 are the same position in
  the sibling cosets `C_a` and `C_{a+1}`. Their subtrees `T_a` and `T_{a+1}` have the same digit
  streams below level 1: `u` on top of the tail.
- **What the links see.** Reader values at level `≥ 1` in either subtree are
  `δ(σ, u·(digits above the tail))`, with `σ ∈ {s, s'}` the subtree's tail choice. By the merge,
  they are independent of `σ` at every site at or above the merge.
- **The free choices are invisible outside.**
  - Any link rule of radius `r` joins a site of `T_a` to a site outside `T_a` only within
    distance `r` of `T_a`'s top.
  - Taking the tail block deep (`|u|` placed below radius `r`, with enough padding), every such
    site lies above the merge.
  - So both choices of `σ` give the same values near the top, and no rule outside `T_a` sees
    `σ`. The same holds for `T_{a+1}`.
- **The fibre splits.** Over this base configuration the fibre therefore contains a product
  `{s, s'} × {s, s'}` of the two subtrees' choices, with no forbidden combination.
- **Non-rigidity.** Put noncommuting idempotents `P`, `P'` on the two subtrees' free letters, as
  in part 3 of `rope-readers-cannot-be-deterministic-and-must-couple-chains`. This gives a
  noncommuting relative family. Lifting then contradicts rigidity.

**3.**
- **Values determine tails.** Injectivity makes `σ ↦ δ(σ, w)` a bijection for every word `w`.
  So the value at any site of a free chain determines its tail state.
- **Links transmit tails.** A link `q(x) = q(y)` between two chains whose digit words below `x`
  and `y` agree therefore identifies their tails. The parent's linking recursion (block links,
  and carries resolved one level down) then joins all free chains.
- **The relative family.** It is determined by the partition of unity `{G_q(u_0)}` at one
  reference site, since every other site's idempotents are permuted copies. A single partition
  of unity commutes.

**4.** This combines parts 1–3 with the fact from `rope-readers-cannot-be-deterministic-and-must-couple-chains` that
residue-periodic sets are exactly the deterministically readable ones.

## Lesson for general BH
- **The finite-state test.** A seed can read a non-periodic index set rigidly only if its
  reader never forgets. Every digit must act injectively, because a merging word hides the
  choice at infinity, and hidden choices in different subtrees are independent.
- **What it excludes.** Absorbing rejection, as in "all digits allowed", is exactly what
  Higman–Clapham ropes use, and it is incompatible with rigid finite-state readers.
- **Where the seed tower now stands.** It needs ropes indexed by group languages, or
  residue-periodic sets. The open question moves from the reader to the machine: can a
  modular machine tolerate group-language ropes?
