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
the existential over `p` collapses.  Worse, *any* row that is an arithmetic
progression with common difference `p` is **dense** in `Z_q` for every
`q != p`, because `p` is invertible modulo `q^m`; so progressions are
maximally visible to the other primes and can never be used.

**A candidate that survives both tests.**  Use factorial powers with a
shift.  Put

```text
row_p(k) = { p^(n!) + c_p : 1 <= n <= k },
```

with `c_p` a fixed integer.  Two computations, one for each topology:

* in `Z_p`, `p^(n!) -> 0`, so the row accumulates at `c_p`; if `c_p` is
  omitted from the set, the row is **not** pro-`p` closed;
* in `Z_q` for `q != p`, the order of `p` modulo `q^m` divides `n!` for all
  large `n`, so `p^(n!) -> 1` and the row accumulates only at `1 + c_p`;
  adjoining that single integer makes the row pro-`q` closed.

So `row_p(k) u {1 + c_p}` is closed in every pro-`q` topology with
`q != p`, and its pro-`p` closedness is exactly the finiteness of `k`.
This is the selective visibility the construction needs.  What remains
before a `Sigma^0_4`-completeness claim can be made is to rule out
*accidental* limit points of the union of all rows: a diagonal sequence
drawn from infinitely many rows could converge in some `Z_q` to an integer
outside the set, and the shifts `c_p` must be chosen (for instance highly
divisible, or congruent to prescribed residues modulo the moduli that
matter for the smaller primes) to prevent it.  That verification has not
been carried out here.
