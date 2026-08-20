---
rg: 2
id: c18-source-cut-has-sparse-relator-certificate-proof
kind: route
title: Sort every C18 monomial and record swaps and square deletions
target: c18-source-cut-has-sparse-relator-certificate
requires:
  - oriented-c18-rank-gates-give-branch-balance
artifacts:
  - experiments/c18_source_cut_certificate.py
---

Expand all ordered atom products in the free projection variables.  The
polynomial `FS-E` has 215 nonzero monomials before reduction.  Deterministically
bubble-sort each word by variable index.  Replacing an adjacent inverted pair
`P_jP_i` by `P_iP_j` records the multiplier of
`P_jP_i-P_iP_j`.  Once sorted, replacing `P_iP_i` by `P_i` records the
multiplier of `P_i^2-P_i`.  Iteration ends in the sorted square-free Boolean
normal form.

The normal form is zero.  Aggregating equal certificates leaves 476
commutator terms and 80 idempotence terms, with coefficient `l1` norm 2112.
The verifier expands those 556 recorded relator multiples back into the free
algebra and checks exact equality with the original 215-monomial difference
over `Z`; it also separately evaluates the identity on all 64 Boolean atoms.
There is no floating-point or randomized step.

Substitution `P_i=(I-Z_i)/2` turns every recorded basic relator into one
quarter of the corresponding group-word involution or commutator defect.
The triangle inequality, contraction of the monomial multipliers, and
`max_r ||r||_2<=sqrt(sum_r||r||_2^2)` give `(CSC3)`.

Finally

```text
FC-EC=(FS-E)C+F(I-S)C.
```

Each of the 20 ordered atom products defining `F` is a contraction, so
`||F||<=20`; `(CSC4)` follows.  In an exact context this specializes to the
projection identity `FS=E`.
