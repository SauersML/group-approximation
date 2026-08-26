---
rg: 2
id: natural-group-properties-realize-the-first-three-levels
kind: claim
title: Natural group properties are complete at each of the first three arithmetical levels, and the fourth is open
artifacts:
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  arithmetical-complexity-table-of-group-properties: that is the ledger of individual cells; this reads the ledger as a hierarchy theorem and isolates the level-four question.
  second-level-rice-theorem-for-local-approximation-properties: that is the engine for level two; this is the statement that the three levels are each realized and the pattern's continuation is open.
---

ESTABLISHED (as a summary of established cells).  On recursive
presentations of groups:

```text
level 1   Kazhdan's property (T)                     Sigma^0_1-complete
level 2   sofic, LEF, operator-MF, amenable,
          metabelian, torsion-free, commutative,
          trivial (and hyperlinear on side (B))      Pi^0_2-complete
level 3   residual finiteness, residual p-finiteness Pi^0_3-complete
          solvability of the word problem            Sigma^0_3-complete
```

so the first three levels of the arithmetical hierarchy are each realized
by a natural, classically studied property of finitely generated groups,
with the completeness proofs in
[[kazhdan-property-t-of-finite-presentations-is-sigma1-complete]],
[[sofic-recognition-two-generator-recursive-is-pi2-complete]],
[[amenability-two-generator-recursive-is-pi2-complete]],
[[torsion-freeness-recognition-is-pi2-complete]],
[[residual-finiteness-two-generator-recursive-is-pi3-complete]],
[[residually-p-two-generator-recursive-is-pi3-complete]] and
[[word-problem-solvability-rec2-is-sigma3-complete]].

## The level-four question

OPEN: is there a natural property of finitely generated groups that is
`Sigma^0_4`- or `Pi^0_4`-complete on recursive presentations?  The natural
candidate is

```text
"G is residually a finite p-group for some prime p",
```

which is `Sigma^0_4` (an existential over primes of the `Pi^0_3` condition
of [[residually-p-two-generator-recursive-is-pi3-complete]]).  Hardness
needs an index family whose pro-`p` closedness is controlled independently
for each prime, i.e. a set `J` that is pro-`q` closed for every `q != p`
while its pro-`p` closedness encodes an arbitrary `Pi^0_3` event.  What
makes this delicate is that no infinite subset of `Z` is invisible to a
given prime: the same congruences are seen by every topology, so the rows
must be designed to have their only accumulation points at prescribed
`p`-adic locations.

## Attempts

The dyadic construction of [[index-set-profinitely-closed-is-pi3-complete]]
does not generalize as written: its rows `2^x(2j+1)` accumulate at `-2^x`
in every profinite topology, so the same failure is seen at every prime and
the existential over `p` collapses.  A prime-indexed variant would have to
place row `p` inside a set that is closed in the pro-`q` topology for
`q != p`; finite rows are closed in all of them, so the difficulty is
exactly to make the *infinite* rows selectively visible.
