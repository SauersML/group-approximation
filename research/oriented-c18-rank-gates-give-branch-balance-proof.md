---
rg: 2
id: oriented-c18-rank-gates-give-branch-balance-proof
kind: route
title: Replace the target-only atom by a second double-source exit and exhaust the frames
target: oriented-c18-rank-gates-give-branch-balance
requires:
  - fanizza-final-bcs-has-fixed-nonlinear-menu
  - ordered-bdd-compresses-predicate-rank-gate
  - fanizza-bad-atoms-have-symmetric-frames
  - corner-localized-non-ce-bcs-energy-gap
artifacts:
  - experiments/fanizza_oriented_c18_exit_compiler.py
---

For `h=1`, enumerate the eight first-triple atoms.  The values of
`(p+q,r,e_1+e_2)` are

```text
000:(0,0,0)   001:(0,1,0)   010:(1,0,1)   011:(1,1,0)
100:(1,0,1)   101:(1,1,0)   110:(2,0,2)   111:(2,1,1).
```

Both inequalities in `(OCB2)` are immediate from this table.  The original
bad first triples are `100,010,001,110,111`.  Intersecting with
`s=[p+q>0]` deletes only `001`, leaving exactly the support of `e_1`; this is
`(OCB3)`.  Multiplication by the four even-parity last triples gives 16 atoms
for `e_1` and four additional occurrences for `e_2`.

The verifier checks all 64 six-bit assignments using ordinary integer
arithmetic before invoking any rank compiler.  It then constructs the best
reduced-OBDD Schur matrix for each exit predicate and applies the exhaustive
dual-word frame search to every satisfying atom.  All 20 searches require
word weight at most two, have the exact kernel in `(OCB4)`, and return the
single hard covector `e_02^*` with both reverse character first bits zero.
There is no randomized or numerical step.

On a joint spectral decomposition of the exactified C18 context, pointwise
order in `(OCB2)` becomes operator order and hence the same normalized-trace
inequalities.  Splitting every occurrence into equal active and exit halves
turns the two integrated inequalities into `(OCB2b)`; both halves are needed.

For the stronger source-packing assertion, `e_2` implies `e_1` pointwise, so
their exact central packet supports satisfy `F_2<=F_1`.  The first gate's
relative Pauli relation forces the two `Q_1` spectral halves to have equal
trace on every `F_1` block.  Consequently the two projections in `(OCB5)`
are orthogonal and have traces `tau(F_1)/2,tau(F_2)/2`.  This realizes the
upper exit mass `x=s/2` inside one source copy even at `110`.

Fixed-word telescoping transfers these identities to the original shared
words with polynomial level cost.  Equation `(OCB3)` permits the localized
BCS gap to be applied before the two local packet exactifications, so no
independent-context classicalization is assumed.  Constructing distinct
next-level images for the active halves is intentionally not asserted here.
