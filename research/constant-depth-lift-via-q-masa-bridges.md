---
rg: 2
id: constant-depth-lift-via-q-masa-bridges
kind: route
title: Use one flip-free q-MASA reset at each of the finitely many contraction levels
target: constant-depth-schur-lift-of-doubling-tape
requires:
  - self-referential-bcs-doubling-tape
  - full-q-masa-forgets-selectors-retains-branches
  - q-masa-to-fresh-packet-morita-bridge
  - finite-schur-clifford-packet-flexible-hs-exactification
  - shared-overlap-controls-packet-multiplicity-vector
  - coherent-sequential-schur-tape-payment
---

Fix the terminal-absorbing depth `m` before constructing the presentation.
At level `n`, restrict the exactified Schur packet first to its corrected `Q`
child and then to `K_f`.  The two active branches have disjoint `K_f`
character supports, while `(QMR2)` ensures the overlap contains none of the
old selector generators.  Apply the one-sided Morita bridge to install the
fresh packet and transport the sum of those supports before any balancing
flip is added.

There are only `m` cells.  Exactify their union as one fixed finite packet and
sum the finitely many shared-overlap errors into one constant.  The BCS
certificate decomposition charges the complementary types exactly as in the
sequential payment theorem.  This yields `(CDS1)` without a shift, an
infinite selector-renewal mechanism, or constants uniform in tower depth.
