---
rg: 2
id: hrf-ghb7-expanding-block-localization
kind: claim
title: Flexible HS instability of a finitely presented Kazhdan group localizes to single growing scalar-expanding blocks in a doubled presentation
distinct_from:
  quotient-gap-gives-large-scalar-expanding-blocks: That supplies physical block decompositions at fixed discarded trace; this assembles flexible rounding across those blocks and selects a single expanding instability witness.
  kazhdan-hs-instability-lives-on-properly-nonamenable-limits: That localizes instability by the amenable summands of a limit algebra; this localizes it to individual coordinate tuples with a fixed scalar gap, retaining doubled generators.
artifacts:
  - research/artifacts/hyperbolic-rf-ghb7-2026-09-20.md
---

For every finitely presented Kazhdan group Gamma, flexible HS stability
is equivalent to the following condition on a doubled finite presentation:
for each fixed c>0, every sequence of approximate presentation tuples
with scalar conjugation gap at least c is flexibly roundable.

The doubled presentation replaces each generator s_j by s_j^+,s_j^-,
uses the original relators in the plus copies, and adds
s_j^+(s_j^-)^-1=1. For 2h generators the scalar gap means

    (8h)^-1 sum_{j,sign} ||[V_j^sign,X]||_2^2
       >= c ||X-tr(X)I||_2^2

for every matrix X in the coordinate dimension. Relator defects tend
to zero in normalized HS norm. Flexible rounding has dimension ratio
tending to one and compression errors tending to zero on both copies.

If stability fails, there is a sequence with one fixed positive c,
dimensions tending to infinity, relator defects tending to zero and
rounding cost bounded below by a fixed positive number. Rounding cost
is the infimum of the maximum of relative dimension inflation and
generator compression errors over genuine representations.

The proof uses Liu Theorem 5.1 exactly at one fixed discarded-trace
tolerance. No scalar gap for the plus tuple alone, or positive gap
uniform as the discarded tolerance tends to zero, is asserted. The
artifact gives the complete weighted Markov and direct-sum argument.

DERIVATION
hrf-ghb7-expanding-block-localization-proof
