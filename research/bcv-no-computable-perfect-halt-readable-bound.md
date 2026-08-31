---
rg: 2
id: bcv-no-computable-perfect-halt-readable-bound
kind: claim
title: No computable bound controls the readable algebra of a perfect BCV HALT strategy
refutes:
  - bcv-halt-completeness-has-computable-readable-factor-bound
distinct_from:
  bcv-canonical-readable-growth-no-computable-bound: that treats only the particular forward completeness strategy; this lower bound holds for every attained-perfect finite-dimensional ZPC strategy of the tailored HALT game.
  computable-bcv-halt-bound-diagonalizes-to-finite-readable-gap: that is a valid conditional implication from the now-refuted bound; this proves that its premise is impossible.
  perfect-gap-zpc-has-finite-readable-translate-algebra: this theorem produces no NONHALT gap strategy and therefore does not solve the group-existence target.
---

**ESTABLISHED (attained finite-dimensional strategies).** Let
`lambda=lambda(M)` be the positive computable parameter from BCV Lemma
2.61, let `V=V_(M,lambda)`, and let

```text
G_M=V_C,
T_0=C,                 T_(j+1)=2^T_j.                    (NHB1)
```

If `M` first halts after `N` steps, put

```text
h=min{j:T_j>=N}.
```

Then every attained-perfect finite-dimensional signed-permutation ZPC
strategy `S` for `G_M` satisfies

```text
dim D_infinity(S)
  >= product_(0<=j<h) 2^(2^(lambda T_j))
  >= 2^h.                                                (NHB2)
```

Consequently there is no total computable function `B` on Turing-machine
descriptions such that every halting `M` has some perfect ZPC strategy for
`G_M` with

```text
dim D_infinity <= B(M).                                  (NHB3)
```

The assertion is universal over perfect strategies, not merely over BCV's
chosen forward completeness strategy. The exact wrapper inverse and Pauli
normal form are essential: value preservation alone would not imply
`(NHB2)`.

This is a negative structural result about one proposed diagonal route. It
does not construct a perfect finite-readable NONHALT gap strategy and does
not prove that a nonhyperlinear group exists. The proof is
`bcv-arbitrary-perfect-halt-readable-diagonal-proof`.
