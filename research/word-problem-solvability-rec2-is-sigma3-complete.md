---
rg: 2
id: word-problem-solvability-rec2-is-sigma3-complete
kind: claim
title: Solvability of the word problem is Sigma-zero-three complete for two-generator recursive presentations, read off the shift graph
distinct_from:
  shift-raag-family-classifies-amenability: that decides amenability of the family by completeness of the shift graph; this observes that the word problem of the family is exactly the membership problem of the index set, so its solvability index set is Rogers' REC.
  uniform-word-problem-on-presentation-codes-undecidable: that is undecidability of the uniform word problem; this is the arithmetical level of the property "has solvable word problem" as an index set.
---

ESTABLISHED.  For recursive presentations on two generators,

```text
SOLVABLE-WP_rec2 = { e : the presented group has decidable word problem }
                   is Sigma^0_3-complete.                              (WP1)
```

For finite presentations the corresponding statement is the classical
theorem of Boone and Rogers (1966); the two-generator recursive version
is immediate from the shift right-angled Artin family
`G_J = < a, t | [a, t^j a t^-j], j in J >`: its word problem is decidable
iff `J` is a decidable set, since `j in J` iff `[a, t^j a t^-j] = 1` in
`G_J` (two vertices of a right-angled Artin group commute iff adjacent)
and, conversely, decidable `J` gives the right-angled Artin normal form
algorithm on the window of a word.  Hence `{e : G_{W_e} has solvable word
problem} = {e : W_e is recursive}`, which is `Sigma^0_3`-complete
(Rogers).  The upper bound `exists algorithm, forall words, correct` is
`Sigma^0_3` for every recursive presentation.
