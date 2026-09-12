---
rg: 2
id: kari-words-give-virtual-formalizability-over-integers
kind: route
title: Regroup along mZ so both block permutations are sitewise and the offset is a linear conjugation
target: reversible-binary-automata-over-integers-virtually-formalizable
requires:
  - reversible-automata-over-integers-are-block-permutation-words
  - sitewise-pairs-over-prime-fields-are-stably-formalizable
  - structurally-reversible-automata-are-formalizable
artifacts:
  - research/artifacts/partitioned-and-regrouped-formalizability-2026-09-12.md
---

Artifact, Sections 2.3 and 3.
1. Regroup along `mZ`, refining so both partitions are unions of blocks. The aligned block permutation
   is sitewise on blocks of at least two bits, so with no identity track it is a formal pair (second
   prerequisite, for `n >= 2`). A one-bit sitewise permutation is affine.
2. The offset block permutation is conjugate to an aligned one by a regrouped translation, a linear
   automaton with a linear inverse. The final translation is linear too.
3. Formal pairs compose (third prerequisite), so the whole word is a formal two-sided pair over `mZ`.
