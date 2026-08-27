---
rg: 2
id: rooted-tree-tail-triviality-proof
kind: route
title: Fix every finite vertex and use faithfulness of the tree action
target: rooted-tree-first-hit-recursion-has-no-infinite-only-tail
requires: []
---

The trivial root permutation fixes the first letter.  On a word beginning
with `0`, the remaining action is again `g`; on a word beginning with
`x!=0`, it is `h_x`.  If all `h_x=1`, induction on word length shows that
every vertex is fixed.  A faithful tree action has trivial kernel, proving
the claim.  For the boundary statement, the complement of the fixed-point
set is open because the diagonal in `X^omega times X^omega` is closed.

The finite-level kernels have finite index and their intersection is the
kernel of the tree action, proving residual finiteness as well.

