---
rg: 2
id: universal-fp2-simple-envelopes-force-uncountably-many
kind: claim
title: If every countable group embeds in a simple FP_2 group, there are continuum many simple FP_2 groups, some not recursively presented
distinct_from:
  simple-envelope-forces-solvable-word-problem: that is Kuznetsov's theorem that finitely presented simple groups have solvable word problem; this uses the recursively presented case of the same argument, together with a counting argument, to derive consequences of universal FP_2 simple envelopes.
  every-countable-group-embeds-in-a-simple-fp2-group: that is the universal envelope statement itself (Zaremsky Problem 1.25); this is an implication out of it, established unconditionally as an implication.
---

**ESTABLISHED** by `universal-fp2-simple-envelopes-force-uncountably-many-proof`.

Suppose every 2-generator group embeds in a simple group of type `FP_2` (over
`Z`). Then:

1. there are exactly `2^ℵ0` isomorphism classes of simple groups of type `FP_2`;
2. some simple group of type `FP_2` has unsolvable word problem; equivalently,
   it is not recursively presented.

So a yes answer to Zaremsky Problem 1.25
(`zaremsky-1-25-countable-groups-embed-in-simple-fp2`) gives a yes answer to the
first part of Zaremsky Problem 1.20 (uncountably many simple groups of type
`FP_2`) and positive answers to both questions of Fournier-Facio–Wu–Zaremsky,
arXiv:2603.24687v2, Remark 4.16. Contrapositively, if only countably many simple
`FP_2` groups exist, Problem 1.25 has answer no.
