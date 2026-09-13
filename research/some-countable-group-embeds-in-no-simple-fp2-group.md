---
rg: 2
id: some-countable-group-embeds-in-no-simple-fp2-group
kind: claim
title: Some countable group embeds in no simple group of type FP_2
distinct_from:
  every-countable-group-embeds-in-a-simple-fp2-group: that is the affirmative answer to Zaremsky Problem 1.25; this is its negation, the negative answer.
---

There is a countable group `H` such that no simple group of type `FP_2`
(over `Z`) contains a copy of `H`.

This is the negative answer to Zaremsky Problem 1.25
(`zaremsky-1-25-countable-groups-embed-in-simple-fp2`).

## Attempts

- **Computability.** The Kuznetsov obstruction that limits finitely presented
  simple envelopes to inputs with solvable word problem needs a recursive
  presentation of the envelope. Groups of type `FP_2` need not be recursively
  presented (Leary), so no computability obstruction is available.
- **Counting.** If there were only countably many simple `FP_2` groups up to
  isomorphism, only countably many finitely generated groups would embed in
  them, while there are continuum many 2-generator groups (B. H. Neumann); that
  would give a negative answer. No such countability result is known, and
  Fournier-Facio–Wu–Zaremsky (arXiv:2603.24687v2, Remark 4.16) list its
  opposite as an open question. This side is not being attacked now.
