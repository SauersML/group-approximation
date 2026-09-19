---
rg: 2
id: bcv-canonical-readable-growth-no-computable-bound
kind: claim
title: The tower-normalized BCV completeness strategy has no computable readable bound
distinct_from:
  bcv-no-computable-perfect-halt-readable-bound: that proves the same tower lower bound for every attained-perfect strategy and strictly strengthens this canonical-strategy corollary.
  computable-bcv-halt-bound-diagonalizes-to-finite-readable-gap: that is a conditional extraction from a premise now known to be false; this is a negative HALT-side result and performs no NONHALT extraction.
  bcv-question-reduction-retains-readable-closure: that treats a single Question Reduction packet; this iterates the entire compression pipeline down the BCV fixed-point tower.
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

Choose a base perfect ZPC strategy at level `T_(h_M)` using BCV's
halting base case, and at the levels

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

There is no total computable function `B` from machine encodings to
natural numbers such that every halting `M` satisfies

```text
dim D_infinity(S_M^can) <= B(M).                         (CRG3)
```

This claim is now an immediate special case of the stronger theorem
`bcv-no-computable-perfect-halt-readable-bound`, which proves `(CRG2)`
for every attained-perfect finite-dimensional ZPC strategy of `G_M`.
That stronger theorem still produces no NONHALT gap witness and no
nonhyperlinear group.
