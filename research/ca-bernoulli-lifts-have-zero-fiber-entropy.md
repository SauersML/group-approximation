---
rg: 2
id: ca-bernoulli-lifts-have-zero-fiber-entropy
kind: claim
title: Every invariant lift of uniform Bernoulli through an automaton has zero fiber entropy
refuted_by:
  - xor-lift-of-bernoulli-has-positive-fiber-entropy
distinct_from:
  strict-split-pairs-carry-positive-entropy-flip-lifts: that proves strict split pairs carry positive-entropy lifts; this is the universal zero-entropy statement that would have turned it into a contradiction, and it is false.
artifacts:
  - research/artifacts/decoder-fiber-flip-lifts-2026-09-12.md
---

**REFUTED.** For every countable group `G`, finite alphabet `A` and cellular
automaton `sigma` on `A^G`, every `G`-invariant probability measure `nu` on `A^G`
with `sigma_* nu` uniform Bernoulli satisfies
`H_nu( x(e) | sigma^-1(Borel) ) = 0`.

Recorded so the tempting inference "strictness gives fiber entropy, and fiber
entropy is impossible" stays visibly dead. It never becomes established, so
`gottschalk-via-flip-lift-and-zero-fiber-entropy` cannot fire.

## Attempts

- *Direct counterexample (2026-09-12).* The XOR automaton over `Z` pushes uniform
  Bernoulli to itself with conditional entropy `log 2`
  (`xor-lift-of-bernoulli-has-positive-fiber-entropy`). The statement fails even
  over an amenable, residually finite group.
- *Averaged form.* Over amenable groups the per-site average of the fiber
  entropy of a lift through a split decoder is bounded above, and that bound is
  what proves surjunctivity there. Over `F_2` the Ornstein–Weiss block map
  pushes a uniform process onto a uniform process with a whole free fiber at
  every site, so no average without the section `tau` can work. An averaged
  statement that uses `tau` is equivalent to the goal. Section 4 of the artifact
  has the details.
