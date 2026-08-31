---
rg: 2
id: bcv-canonical-readable-growth-diagonal-proof
kind: route
title: Bound compression depth and decide halting by a computable tower
target: bcv-canonical-readable-growth-no-computable-bound
requires:
  - bcv-honest-compression-amplifies-readable-closure
  - bcv-perfect-answer-reduction-decodes-double-cover
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

The finite-field floor in BCV's robust soundness estimate is not an exact
value-one obstruction. The claim
`bcv-perfect-answer-reduction-decodes-double-cover` proves directly from
Definition 5.79 that every attained perfect Answer Reduced strategy has a
single joint PVM of polynomial-table atoms. The reason is specific to zero
loss: equation `(181)) with `s=0) supplies a DLine through every pair of
points, so their PVMs are exact coarse-grainings of one line PVM and commute.
ALine restrictions then make each joint atom individual-degree nine, and the
pointwise PCP checks decode every supported atom. For a perfect ZPC model the
decoder preserves the readable/unreadable typing and gives

```text
D_infinity(decoded DoubleCover source)
    subseteq D_infinity(target).                         (CRG4)
```

The actual source fed from Question Reduction is bipartite after detyping,
so Remark 3.55 removes the double cover exactly. Thus Answer Reduction no
longer blocks an exact backward analysis of arbitrary attained-perfect
strategies.

This correction does not by itself upgrade the honest lower bound
`(CRG2)` to every perfect strategy of `G_M). Such an upgrade must also
show that an arbitrary strategy can be carried backward through the
remaining compression wrappers and that the Pauli normal form of BCV
Remark 4.22 embeds its full `ell^infinity(F_2^k)` factor, with the required
readable typing, into the original strategy's `D_infinity). Merely
obtaining a perfect decoded source strategy does not prove that block
inclusion. Until that separate universal-amplification statement is
established, this route still rules out a computable bound only for the
published forward construction and does not close
`bcv-halt-completeness-has-computable-readable-factor-bound`.
