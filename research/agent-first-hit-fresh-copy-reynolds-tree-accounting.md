---
rg: 2
id: agent-first-hit-fresh-copy-reynolds-tree-accounting
kind: route
title: Sum the transported atoms before applying the fresh BCS gap
target: agent-first-hit-fresh-copy-reynolds-tree-is-contractive
requires:
  - role-packed-bcs-gap-is-one-idempotent
  - index-two-reynolds-atoms-have-orthogonal-hnn-transports
  - independent-address-capacity-cannot-drive-selected-atom-growth
---

Exact HNN covariance gives `(FCT2)` and trace invariance gives
`tau(D_(n,i))=tau(A_(n,i))`.  Orthogonality of both source and destination
families then gives `(FCT4)` by summing.  Applying the robust BCS lower bound
separately on every active node and summing the fixed finite error terms gives
`(FCT5)`.  Iteration proves `(FCT7)--(FCT8)`.

The cumulative-carrier modification has two cases.  If the new BCS tuple is
supported only on `Q_n`, its soundness lower bound is still proportional only
to `q_n`.  If it is supported on `C_n`, then a destination outside `C_n` must
be distinguished from all old layers by a common address algebra.  The source
and destination become disjoint character cylinders in that algebra, so their
canonical capacities add and obey the Kraft bound.  Adding an independent bit
without restricting the old carrier does not make its target atom orthogonal
to the old carrier; restricting the old carrier to one sign pays exactly the
factor apparently gained by the other sign.

