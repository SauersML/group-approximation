---
rg: 2
id: one-common-intertwiner-carries-the-four-pauli-pi-bridge
kind: claim
title: One common full-support intertwiner carries the four-Pauli PI bridge
distinct_from:
  common-corner-mutual-bicommutant-extraction: that identifies two complete mutual commutant algebras and excludes every spectator; this asks only for one common intertwiner for four fixed word occurrences and is invariant under external amplification.
  one-cross-gram-moment-extracts-the-common-polar-gauge: that aligns two transports of the same packet from a near-full cross-Gram moment; this requires the resulting common polar map to intertwine both transverse Pauli pairs on the fixed PI carrier.
  canonical-trace-forbids-literal-pi-return: that rules out placing outside target words in the literal finite source subgroup algebra; this permits a matrix-coordinate recovered degree-two source factor and asks only for a common intertwiner into it.
---

In every sufficiently accurate canonical microstate of the selected
rectangular compressor cell, recover on one projection `P`, with
`tau(P)>=alpha>0`, the following fixed data:

1. four contractions `C_1,...,C_4` in one exactified algebra
   `B_P ~= M_2 tensor I`;
2. the four fixed transverse target words `D_1,...,D_4`, satisfying the two
   Pauli anticommutators and four cross-commutators with total error `o(1)`;
3. one contraction `T in P M_d P` with
   `||T^*T-P||_2+||TT^*-P||_2=o(1)` and

```text
sum_(j=1)^4 ||D_j T-T C_j||_2=o(1).                    (CPI1)
```

All four occurrences in `(CPI1)` must use the same `T`, and their total
error must be bounded by a dimension-independent constant times the selected
cell's word/transport defect.  The factor `B_P` is allowed arbitrary external
multiplicity; no claim that its commutant is word-generated or scalar is
made.

This is the smallest direct word-visibility lemma surviving the exact
rectangular test.  Telescoping the 24 degree-four monomials gives

```text
||s4(D)T-Ts4(C)||_2
 <= 24 sum_j ||D_jT-TC_j||_2.                           (CPI2)
```

Amitsur--Levitzki makes `s4(C)=0`, while the Pauli table and
`tau(P)>=alpha` give `||s4(D)||_2>=8sqrt(alpha)-o(1)`.
The almost-unitarity of `T` transfers this lower bound to `s4(D)T`,
contradicting `(CPI2)`.  Spectator amplification tensors every term with the
identity and leaves the argument unchanged.
