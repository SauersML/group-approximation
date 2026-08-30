---
rg: 2
id: bcv-canonical-readable-growth-no-computable-bound
kind: claim
title: The tower-normalized BCV completeness strategy has no computable readable bound
distinct_from:
  bcv-halt-completeness-has-computable-readable-factor-bound: that asks for a computable bound on some possibly different perfect strategy for each halting machine; this rules out a bound only for one explicitly normalized use of the published completeness construction.
  computable-bcv-halt-bound-diagonalizes-to-finite-readable-gap: that uses an existential HALT-side bound to extract a bounded-factor NONHALT witness; this is a negative result about the canonical HALT-side construction and performs no such extraction.
  bcv-question-reduction-retains-readable-closure: that treats a single honest Question Reduction; this iterates the whole honest compression pipeline down the BCV completeness tower.
---

For the BCV verifier `V=V_(M,lambda)` and its fixed output level `C`,
define

```text
T_0=C,                 T_(j+1)=2^T_j.                    (CRG1)
```

Suppose `M` first halts after `N` steps and put

```text
h_M=min{j:T_j>=N}.
```

Choose a base perfect ZPC strategy at level `T_(h_M)` using BCV's halting
base case, and at the levels

```text
T_(h_M-1),...,T_0
```

apply the particular perfect strategies in the published compression
completeness proofs. Denote the resulting perfect strategy for
`G_M=V_C` by `S_M^can`. Then

```text
dim D_infinity(S_M^can)
  >= product_(0<=j<h_M) 2^(2^(lambda T_j))
  >= 2^h_M.                                              (CRG2)
```

There is no total computable function `B` from machine encodings to natural
numbers such that every halting `M` satisfies

```text
dim D_infinity(S_M^can) <= B(M).                         (CRG3)
```

This does not refute the claim that some other perfect strategy for `G_M`
might admit a total computable readable-factor bound.
