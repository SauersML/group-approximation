---
rg: 2
id: c18-source-cut-has-sparse-relator-certificate
kind: claim
title: The C18 forward-source cut has a fixed sparse ordered-polynomial certificate
artifacts:
  - experiments/c18_source_cut_certificate.py
distinct_from:
  oriented-c18-rank-gates-give-branch-balance: that proves the Boolean trace ledger after exact context decomposition; this gives a dimension-free noncommutative transfer bound on the original shared words.
  corner-localized-non-ce-bcs-energy-gap: that supplies forbidden mass on an approximately reducing carrier but does not identify which oriented atom receives C18 mass; this performs that source-local identification.
---

Let `P_0,...,P_5` be six formal projections in the fixed C18 order.  Write
`A_a` for the ordered atom product, let

```text
F=sum_(a forbidden for C18) A_a,
S=P_0+P_1-P_0P_1,
E=sum_(a satisfying e_1) A_a.
```

There is an explicit identity in the free algebra

```text
FS-E
 = sum_t lambda_t V_t R_t W_t,                         (CSC1)
```

where each `R_t` is either `[P_i,P_j]` or `P_i^2-P_i`, every `V_t,W_t` is a
monomial, there are 556 nonzero terms after aggregation, the total coefficient
weight is

```text
sum_t |lambda_t|=2112,                                 (CSC2)
```

and no expanded word has length greater than eight.

For unitary words `Z_i`, put `P_i=(I-Z_i)/2`.  Since

```text
[P_i,P_j]=[Z_i,Z_j]/4,
P_i^2-P_i=(Z_i^2-I)/4,
```

all monomial multipliers are contractions and `(CSC1)` gives

```text
||FS-E||_2 <= 528 sqrt(E_C18),                          (CSC3)
```

where `E_C18` is the sum of squared involution and pairwise-commutator defects
for the six original shared context words.

If `C` is a source carrier with `||(I-S)C||_2<=epsilon_source`, then

```text
||FC-EC||_2
 <= 528 sqrt(E_C18)+20 epsilon_source.                 (CSC4)
```

Thus the equality `F_C18 S=e_1` survives quantitatively before independent
packet exactification.  It requires no common classical assignment decoder.
