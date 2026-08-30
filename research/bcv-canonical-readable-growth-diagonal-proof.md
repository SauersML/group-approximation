---
rg: 2
id: bcv-canonical-readable-growth-diagonal-proof
kind: route
title: Bound compression depth and decide halting by a computable tower
target: bcv-canonical-readable-growth-no-computable-bound
requires:
  - bcv-honest-compression-amplifies-readable-closure
---

If `j<h_M`, then `T_j<N`, so the machine has not halted by level `T_j`.
BCV Lemma 2.59 identifies the game at that level with its compressed
fixed-point branch. Since `T_(j+1)=2^T_j`, one application of compression
completeness carries a perfect strategy from level `T_(j+1)` to level
`T_j`.

At this compression step, Question Reduction uses Pauli parameter

```text
k(T_j)=2^(lambda T_j).
```

The honest-compression prerequisite multiplies readable dimension by at least
`2^k(T_j)`. Iterating proves the product in `(CRG2)`; the weaker lower
bound `2^h_M` follows because every factor is at least two.

Assume that a total computable `B` satisfies `(CRG3)`. Given `M`,
compute `B(M)`, `lambda`, and `C`, and let

```text
r=floor(log_2(max(1,B(M))))+1.
```

Compute the tower value `T_r` from `(CRG1)` and simulate `M` for
`T_r` steps. If it halts, answer HALT. If it has not halted but later halts
at time `N`, then `N>T_r`, so `h_M>=r+1`. Equation `(CRG2)` gives

```text
dim D_infinity(S_M^can) >= 2^h_M > B(M),
```

contradicting `(CRG3)`. Hence failure to halt by `T_r` proves that `M`
never halts. This would decide the halting problem, so no such `B` exists.

## Exact boundary

The same argument cannot presently be applied to every perfect strategy of
`G_M`. BCV Remark 4.22 does give an exact Pauli decomposition and an honest
source strategy from every perfect Question Reduction strategy. Answer
Reduction is different: Theorem 5.1 gives, from target error `epsilon`,
source error bounded by

```text
c((n lambda)^c epsilon^(1/c)+(n lambda)^(-1/c)).          (CRG4)
```

The second term remains when `epsilon=0`. Its low-individual-degree
extraction has the analogous finite-field `q^(-1)` slack. Point-line
consistency on the test incidence graph does not by itself give a single
joint PVM for all unreadable point evaluations; Z-alignment makes all
readable point observables diagonal but does not force the unreadable
observables at different points to commute. Thus there is no established
exact inverse that would carry an arbitrary perfect answer-reduced ZPC
strategy back to a perfect source ZPC strategy while retaining readable
closure.

Accordingly, this route rules out a uniform reset in the published forward
construction, but it neither disproves
`bcv-halt-completeness-has-computable-readable-factor-bound` nor closes the
nonhyperlinear-group source premise.
