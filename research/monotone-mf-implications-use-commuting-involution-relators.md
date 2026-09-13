---
rg: 2
id: monotone-mf-implications-use-commuting-involution-relators
kind: claim
title: Explicit independent commuting involution relators implement every monotone MF implication with near-linear total word length
root: true
distinct_from:
  lef-kazhdan-mf-closure-realizes-monotone-boolean-rules: that uses normal input subgroups; this supplies one explicit involution word per input and one output word, an executable compiler and a total length bound.
artifacts:
  - research/artifacts/pestov91-short-involution-mf-implications-2026-09-13.md
  - research/artifacts/compile-pestov91-mf-implication-words-2026-09-13.py
---

For a positive formula with `s` variable occurrences, one constructs
a LEF Kazhdan group on torsion generators of orders `7,2,2`, with
decidable word problem, and independent commuting involution words
`a_1,...,a_m,b`. Every named variable is assumed to occur.

All MF-target maps killing the `a_i` for `i in I` kill `b` exactly
when the formula is true on `1_I`. Otherwise an explicit LEF quotient
with decidable word problem kills those inputs and preserves `b`.
The output remains nontrivial in every ordinary input quotient.
The total expanded word length is at most `256(s+1)ell^2`, where
`ell=2 ceil(log_2 M)+4` and `M<=3s+3`.

For the conjunction of all inputs every proper selection of the
relators gives a LEF quotient and the full selection gives a just
non-MF quotient, including the single-relator case.
